module

public import CFSG.RankThree.GF2n.Stroth80.Sec85CommAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {M Q : Subgroup G}

theorem mem_bar_iff_exists_lift [(Q.subgroupOf M).Normal] {S : Subgroup G} {u : Mbar M Q} :
    u ∈ bar M Q S ↔ ∃ g : ↥M, (g : G) ∈ S ∧ QuotientGroup.mk' (Q.subgroupOf M) g = u := by
  constructor
  · intro hu
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.mp hu
    exact ⟨s, Subgroup.mem_subgroupOf.mp hs, hsu⟩
  · rintro ⟨g, hg, rfl⟩
    exact Subgroup.mem_map.mpr ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem commutator_mem_iff_bar [(Q.subgroupOf M).Normal] (a b : ↥M) :
    (⁅(a : G), (b : G)⁆ ∈ Q) ↔
      ⁅QuotientGroup.mk' (Q.subgroupOf M) a, QuotientGroup.mk' (Q.subgroupOf M) b⁆ = 1 := by
  rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem sec85_comm_core_mod [Finite G] {R N Zc : Subgroup G} {x y : G}
    (hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hRM : R ≤ M) (hNR : N ≤ R) (hQZ : Q ≤ Zc)
    (hZN : Zc ≤ N) (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hN2 : IsPGroup 2 ↥N)
    (hZc : ∀ z ∈ Zc, ∀ r ∈ R, ⁅z, r⁆ ∈ Q) (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Zc)
    (hNsq : ∀ n ∈ N, n ^ 2 ∈ Zc) (hZ : ∀ a ∈ N, (∀ b ∈ N, ⁅a, b⁆ ∈ Q) → a ∈ Zc)
    (hperf : ∀ r ∈ R, ∃ a ∈ ⁅R, R⁆, ∃ k ∈ N, r = a * k) (hxM : x ∈ M)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxR : ∀ r ∈ R, ⁅r, x⁆ ∈ N)
    (hxZ : ∀ z ∈ Zc, ⁅x, z⁆ ∈ Q) (hxNZ : ∀ n ∈ N, ⁅x, n⁆ ∈ Zc) (hyR : y ∈ R)
    (hy3 : y ^ 3 = 1) (hfpf : ∀ n ∈ N, ⁅y, n⁆ ∈ Zc → n ∈ Zc) :
    ∃ n₀ ∈ N, ∀ r ∈ R, ⁅r, x * n₀⁆ ∈ Q := by
  classical
  haveI hQ : (Q.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn⟩
  set π : ↥M →* Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) with hπ
  have hQN : Q ≤ N := hQZ.trans hZN
  have hbar : ∀ (S : Subgroup G) (g : ↥M), Q ≤ S → (π g ∈ bar M Q S ↔ (g : G) ∈ S) :=
    fun S g hQS => mk_mem_bar_iff_sec4 hQS g
  have hcomm : ∀ a b : ↥M, ⁅(a : G), (b : G)⁆ ∈ Q ↔ ⁅π a, π b⁆ = 1 := commutator_mem_iff_bar
  have elt : ∀ {S : Subgroup G} (u : Mbar M Q), u ∈ bar M Q S →
      ∃ g : ↥M, (g : G) ∈ S ∧ π g = u := fun u hu => mem_bar_iff_exists_lift.mp hu
  have ofel : ∀ {S : Subgroup G} (g : ↥M), (g : G) ∈ S → π g ∈ bar M Q S := fun g hg =>
    mem_bar_iff_exists_lift.mpr ⟨g, hg, rfl⟩
  have hRMn : ∀ r : G, r ∈ R → r ∈ M := fun r hr => hRM hr
  let xM : ↥M := ⟨x, hxM⟩
  let yM : ↥M := ⟨y, hRM hyR⟩
  have hcommR : ∀ (a : G) (ha : a ∈ M), a ∈ ⁅R, R⁆ →
      π ⟨a, ha⟩ ∈ ⁅bar M Q R, bar M Q R⁆ := by
    intro a ha haR
    have hle : ⁅R, R⁆ ≤ Subgroup.map M.subtype ((⁅bar M Q R, bar M Q R⁆).comap π) := by
      refine Subgroup.commutator_le.mpr fun r hr s hs => ?_
      refine ⟨⁅(⟨r, hRM hr⟩ : ↥M), (⟨s, hRM hs⟩ : ↥M)⁆, ?_, ?_⟩
      · show π ⁅(⟨r, hRM hr⟩ : ↥M), (⟨s, hRM hs⟩ : ↥M)⁆ ∈ ⁅bar M Q R, bar M Q R⁆
        rw [map_commutatorElement]
        exact Subgroup.commutator_mem_commutator (ofel _ hr) (ofel _ hs)
      · simp [commutatorElement_def]
    obtain ⟨u, hu, hua⟩ := hle haR
    have : u = ⟨a, ha⟩ := Subtype.ext hua
    rw [← this]
    exact hu
  have key := sec85_comm_core (H := Mbar M Q) (R := bar M Q R) (N := bar M Q N) (Zc := bar M Q Zc)
    (x := π xM) (y := π yM)
    (fun u hu => by
      obtain ⟨g, hg, rfl⟩ := elt u hu
      exact ofel g (hNR hg))
    (fun r hr n hn => by
      obtain ⟨rg, hrg, rfl⟩ := elt r hr
      obtain ⟨ng, hng, rfl⟩ := elt n hn
      rw [← map_inv, ← map_mul, ← map_mul]
      exact ofel _ (by simpa using hNn _ hrg _ hng))
    (by
      have h1 : IsPGroup 2 ↥(N.subgroupOf M) := hN2.comap_subtype
      exact h1.map π)
    (fun u hu => by
      obtain ⟨g, hg, rfl⟩ := elt u hu
      exact ofel g (hZN hg))
    (fun z hz r hr => by
      obtain ⟨zg, hzg, rfl⟩ := elt z hz
      obtain ⟨rg, hrg, rfl⟩ := elt r hr
      have h1 := (hcomm zg rg).mp (hZc _ hzg _ hrg)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm)
    (fun a ha b hb => by
      obtain ⟨ag, hag, rfl⟩ := elt a ha
      obtain ⟨bg, hbg, rfl⟩ := elt b hb
      rw [← map_commutatorElement]
      exact ofel _ (by simpa [commutatorElement_def] using hNN _ hag _ hbg))
    (fun n hn => by
      obtain ⟨ng, hng, rfl⟩ := elt n hn
      rw [← map_pow]
      exact ofel _ (by simpa using hNsq _ hng))
    (fun a ha hab => by
      obtain ⟨ag, hag, rfl⟩ := elt a ha
      refine ofel _ (hZ _ hag fun b hb => ?_)
      have hbm : b ∈ M := hRM (hNR hb)
      have h1 := hab (π ⟨b, hbm⟩) (ofel _ hb)
      exact (hcomm ag ⟨b, hbm⟩).mpr (commutatorElement_eq_one_iff_mul_comm.mpr h1))
    (fun r hr => by
      obtain ⟨rg, hrg, rfl⟩ := elt r hr
      obtain ⟨a, haR, k, hkN, hrk⟩ := hperf _ hrg
      have hcR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le.mpr fun r hr s hs => by
        have e : ⁅r, s⁆ = r * s * r⁻¹ * s⁻¹ := commutatorElement_def r s
        rw [e]
        exact R.mul_mem (R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)) (R.inv_mem hs)
      have haM : a ∈ M := hRM (hcR haR)
      have hkM : k ∈ M := hRM (hNR hkN)
      have hrk' : rg = ⟨a, haM⟩ * ⟨k, hkM⟩ := Subtype.ext hrk
      refine ⟨π ⟨a, haM⟩, hcommR a haM haR, π ⟨k, hkM⟩, ofel _ hkN, ?_⟩
      rw [← map_mul, ← hrk'])
    (fun n hn => by
      obtain ⟨ng, hng, rfl⟩ := elt n hn
      rw [← map_mul, ← map_inv, ← map_mul]
      exact ofel _ (by simpa using hxN _ hng))
    (fun r hr => by
      obtain ⟨rg, hrg, rfl⟩ := elt r hr
      rw [← map_commutatorElement]
      exact ofel _ (by simpa [commutatorElement_def] using hxR _ hrg))
    (fun z hz => by
      obtain ⟨zg, hzg, rfl⟩ := elt z hz
      exact (hcomm xM zg).mp (hxZ _ hzg))
    (fun n hn => by
      obtain ⟨ng, hng, rfl⟩ := elt n hn
      rw [← map_commutatorElement]
      exact ofel _ (by simpa [commutatorElement_def] using hxNZ _ hng))
    (ofel yM hyR)
    (by
      rw [← map_pow]
      have : yM ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one])
    (fun n hn hyn => by
      obtain ⟨ng, hng, rfl⟩ := elt n hn
      rw [← map_commutatorElement] at hyn
      exact ofel _ (hfpf _ hng (by
        have := (hbar Zc ⁅yM, ng⁆ hQZ).mp hyn
        simpa [commutatorElement_def] using this)))
  obtain ⟨n₀', hn₀', hall⟩ := key
  obtain ⟨ng, hng, rfl⟩ := elt n₀' hn₀'
  refine ⟨ng, hng, fun r hr => ?_⟩
  have hrM : r ∈ M := hRM hr
  have h1 := hall (π ⟨r, hrM⟩) (ofel _ hr)
  rw [← map_mul, ← map_commutatorElement] at h1
  have h2 := (hcomm ⟨r, hrM⟩ (xM * ng)).mpr (by rwa [map_mul])
  simpa using h2

end CFSG.RankThree.GF2n.Stroth80
