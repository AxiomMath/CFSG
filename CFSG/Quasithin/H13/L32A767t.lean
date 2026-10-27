module

public import CFSG.Quasithin.H13.L32A767s
public import CFSG.Quasithin.H13.L32A767r

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_centralizer {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (E : Set G), ∀ c ∈ Subgroup.centralizer (E : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro e he
    have he' : x⁻¹ * e * x ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) e).mp he
      simpa using this
    have := hc _ he'
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * e := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem exists_lift_three_comm {E X : Subgroup G} (hU : IsElemAbelian 2 E)
    (hXE : X ≤ Subgroup.normalizer (E : Set G))
    (h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (E : Set G))) {x₀ : G} (hx₀ : x₀ ∈ X)
    (hx₀3 : x₀ ^ 3 = 1) {c : MulAut (IntMod E hU)} (hc : c ∈ autI hU X) (hc3 : c ^ 3 = 1)
    (hcomm : Commute (convI hU ⟨x₀, hXE hx₀⟩) c) :
    ∃ x : G, ∃ hx : x ∈ X, convI hU ⟨x, hXE hx⟩ = c ∧ x ^ 3 = 1 ∧ Commute x₀ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgX, hgc⟩ := (mem_autI hU).1 hc
  set N := X ⊓ Subgroup.centralizer (E : Set G) with hN
  have hA : IsPGroup 3 ↥(Subgroup.zpowers x₀) := fun y =>
    ⟨1, Subtype.ext (by simpa using (isElemAbelian_zpowers_of_pow hx₀3).2 y y.2)⟩
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hAN : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx₀)
      (mem_normalizer_centralizer (hXE hx₀)))
  have hb : ∀ a ∈ Subgroup.zpowers x₀, (g : G)⁻¹ * (a * g * a⁻¹) ∈ N := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hkX : x₀ ^ k ∈ X := zpow_mem hx₀ k
    have hkN : x₀ ^ k ∈ Subgroup.normalizer (E : Set G) := zpow_mem (hXE hx₀) k
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hgX) (mul_mem (mul_mem hkX hgX) (inv_mem hkX)),
      ?_⟩
    have hmem : (g : G)⁻¹ * (x₀ ^ k * g * (x₀ ^ k)⁻¹) ∈ Subgroup.normalizer (E : Set G) :=
      mul_mem (inv_mem g.2) (mul_mem (mul_mem hkN g.2) (inv_mem hkN))
    refine (convI_eq_one_iff hU ⟨_, hmem⟩).1 ?_
    have e : (⟨_, hmem⟩ : ↥(Subgroup.normalizer (E : Set G))) =
        g⁻¹ * ((⟨x₀, hXE hx₀⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ k * g *
          ((⟨x₀, hXE hx₀⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ k)⁻¹) :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, hgc,
      ((hcomm.zpow_left k).eq), mul_inv_cancel_right, inv_mul_cancel]
  obtain ⟨n, hnN, hfix⟩ := exists_mem_coset_centralizer hA hN3 hAN hb
  set y : G := (g : G) * n with hy
  have hyX : y ∈ X := mul_mem hgX hnN.1
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := hXE hyX
  have hyc : convI hU ⟨y, hyN⟩ = c := by
    have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G))) =
        g * ⟨n, hXE hnN.1⟩ := rfl
    rw [e, map_mul, hgc, (convI_eq_one_iff hU ⟨n, hXE hnN.1⟩).2 hnN.2, mul_one]
  have hy3N : y ^ 3 ∈ N := by
    refine ⟨pow_mem hyX 3, (convI_eq_one_iff hU ⟨y ^ 3, pow_mem hyN 3⟩).1 ?_⟩
    have e : (⟨y ^ 3, pow_mem hyN 3⟩ : ↥(Subgroup.normalizer (E : Set G))) = ⟨y, hyN⟩ ^ 3 :=
      Subtype.ext (by simp)
    rw [e, map_pow, hyc, hc3]
  obtain ⟨m, hm⟩ := h2 ⟨_, hy3N⟩
  have hm' : (y ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hpow : ∀ j : ℕ, c ^ 4 ^ j = c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, show 4 = 3 + 1 by rfl, pow_succ, hc3, one_mul]
  have hyx₀ : Commute x₀ y := by
    have := hfix x₀ (Subgroup.mem_zpowers x₀)
    show x₀ * y = y * x₀
    calc x₀ * y = x₀ * y * x₀⁻¹ * x₀ := by group
      _ = y * x₀ := by rw [this]
  refine ⟨y ^ 4 ^ m, pow_mem hyX _, ?_, ?_, hyx₀.pow_right _⟩
  · have e : (⟨y ^ 4 ^ m, hXE (pow_mem hyX _)⟩ : ↥(Subgroup.normalizer (E : Set G))) =
        ⟨y, hyN⟩ ^ 4 ^ m := Subtype.ext (by simp)
    rw [e, map_pow, hyc, hpow]
  · rw [← pow_mul, mul_comm, pow_mul, show (4 : ℕ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num,
      pow_mul, hm', one_pow]

theorem false_of_conj_eq_or_inv (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {E : Subgroup G} (hU : IsElemAbelian 2 E)
    (hXE : dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (E : Set G))
    (hV1E : fsuV1 T V ≤ E) {c : MulAut (IntMod E hU)}
    (hc : c ∈ autI hU (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1)
    (hcR : ∀ r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), ∀ hr : r ∈ Subgroup.normalizer (E : Set G),
      convI hU ⟨r, hr⟩ * c * (convI hU ⟨r, hr⟩)⁻¹ = c ∨
        convI hU ⟨r, hr⟩ * c * (convI hU ⟨r, hr⟩)⁻¹ = c⁻¹) : False := by
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set X := dK T V ⊔ R with hX
  have hRE : R ≤ Subgroup.normalizer (E : Set G) := le_sup_right.trans hXE
  have hCR : X ⊓ Subgroup.centralizer (E : Set G) ≤ R := fun x hx =>
    inf_hz_le_R1 h hMod h63 ⟨hx.1, Subgroup.centralizer_le hV1E hx.2⟩
  have h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (E : Set G)) :=
    (pCoreOf_isPGroup 2 _).to_le hCR
  obtain ⟨y, hyX, hyc, hy3, -⟩ := exists_lift_three_comm hU hXE h2 (one_mem X) (one_pow 3) hc hc3
    (by rw [show (⟨1, hXE (one_mem X)⟩ : ↥(Subgroup.normalizer (E : Set G))) = 1 from rfl,
      map_one]; exact Commute.one_left c)
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hc1
    rw [← hyc]
    exact map_one _
  set P : Subgroup G := ((Subgroup.centralizer ({c} : Set (MulAut (IntMod E hU)))).comap
    (convHom hU R hRE)).map R.subtype with hP
  have hmemP : ∀ x : G, x ∈ P ↔ ∃ hx : x ∈ R,
      convI hU ⟨x, hRE hx⟩ * c = c * convI hU ⟨x, hRE hx⟩ := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.2, Subgroup.mem_centralizer_singleton_iff.mp hr⟩
    · rintro ⟨hx, hcx⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcx, rfl⟩
  have hPR : P ≤ R := Subgroup.map_subtype_le _
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    obtain ⟨hxR, hxc⟩ := (hmemP x).mp hx
    have hrxR : r * x * r⁻¹ ∈ R := mul_mem (mul_mem hr hxR) (inv_mem hr)
    refine (hmemP _).mpr ⟨hrxR, ?_⟩
    have e : convI hU ⟨r * x * r⁻¹, hRE hrxR⟩ = convI hU ⟨r, hRE hr⟩ *
        convI hU ⟨x, hRE hxR⟩ * (convI hU ⟨r, hRE hr⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    set ρ := convI hU ⟨r, hRE hr⟩ with hρ
    set ξ := convI hU ⟨x, hRE hxR⟩ with hξ
    rcases hcR r hr (hRE hr) with h1 | h1
    · calc ρ * ξ * ρ⁻¹ * c = ρ * ξ * ρ⁻¹ * (ρ * c * ρ⁻¹) := by rw [h1]
        _ = ρ * (ξ * c) * ρ⁻¹ := by group
        _ = ρ * (c * ξ) * ρ⁻¹ := by rw [hxc]
        _ = (ρ * c * ρ⁻¹) * (ρ * ξ * ρ⁻¹) := by group
        _ = c * (ρ * ξ * ρ⁻¹) := by rw [h1]
    · have hxc' : ξ * c⁻¹ = c⁻¹ * ξ := by
        calc ξ * c⁻¹ = c⁻¹ * (c * ξ) * c⁻¹ := by group
          _ = c⁻¹ * (ξ * c) * c⁻¹ := by rw [hxc]
          _ = c⁻¹ * ξ := by group
      have h2 : ρ * c⁻¹ * ρ⁻¹ = c := by
        rw [show ρ * c⁻¹ * ρ⁻¹ = (ρ * c * ρ⁻¹)⁻¹ by group, h1, inv_inv]
      calc ρ * ξ * ρ⁻¹ * c = ρ * ξ * ρ⁻¹ * (ρ * c⁻¹ * ρ⁻¹) := by rw [h2]
        _ = ρ * (ξ * c⁻¹) * ρ⁻¹ := by group
        _ = ρ * (c⁻¹ * ξ) * ρ⁻¹ := by rw [hxc']
        _ = (ρ * c⁻¹ * ρ⁻¹) * (ρ * ξ * ρ⁻¹) := by group
        _ = c * (ρ * ξ * ρ⁻¹) := by rw [h2]
  have hinv : ∀ (a : G) (ha : a ∈ R), a ∉ P →
      convI hU ⟨a, hRE ha⟩ * c * (convI hU ⟨a, hRE ha⟩)⁻¹ = c⁻¹ := by
    intro a ha haP
    rcases hcR a ha (hRE ha) with h1 | h1
    · exfalso
      refine haP ((hmemP a).mpr ⟨ha, ?_⟩)
      calc convI hU ⟨a, hRE ha⟩ * c
          = convI hU ⟨a, hRE ha⟩ * c * (convI hU ⟨a, hRE ha⟩)⁻¹ * convI hU ⟨a, hRE ha⟩ := by
            group
        _ = c * convI hU ⟨a, hRE ha⟩ := by rw [h1]
    · exact h1
  have hidx : P.relIndex R ≤ 2 := by
    refine relIndex_le_two_of fun a ha b hb haP hbP => ?_
    refine (hmemP _).mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
    have e : convI hU ⟨a⁻¹ * b, hRE (mul_mem (inv_mem ha) hb)⟩ =
        (convI hU ⟨a, hRE ha⟩)⁻¹ * convI hU ⟨b, hRE hb⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e]
    have hca := hinv a ha haP
    have hcb := hinv b hb hbP
    set α := convI hU ⟨a, hRE ha⟩ with hα
    set β := convI hU ⟨b, hRE hb⟩ with hβ
    have hca' : α⁻¹ * c⁻¹ * α = c := by
      rw [← hca]
      group
    calc α⁻¹ * β * c = α⁻¹ * (β * c * β⁻¹) * β := by group
      _ = α⁻¹ * c⁻¹ * β := by rw [hcb]
      _ = (α⁻¹ * c⁻¹ * α) * (α⁻¹ * β) := by group
      _ = c * (α⁻¹ * β) := by rw [hca']
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := hXE hyX
  have hyP : y ∈ Subgroup.normalizer (P : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    obtain ⟨hxR, hxc⟩ := (hmemP x).mp hx
    have hxX : x ∈ X := Subgroup.mem_sup_right hxR
    have hyx : y * x * y⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      mul_mem (mul_mem hyN (hRE hxR)) (inv_mem hyN)
    have e : convI hU ⟨y * x * y⁻¹, hyx⟩ = convI hU ⟨x, hRE hxR⟩ := by
      have e1 : (⟨y * x * y⁻¹, hyx⟩ : ↥(Subgroup.normalizer (E : Set G))) =
          ⟨y, hyN⟩ * ⟨x, hRE hxR⟩ * (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G)))⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv, hyc, ← hxc, mul_inv_cancel_right]
    have hcomm : y * x * y⁻¹ * x⁻¹ ∈ R := by
      refine hCR (Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem (mul_mem hyX hxX) (inv_mem hyX)) (inv_mem hxX), ?_⟩)
      have hm : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
        mul_mem hyx (inv_mem (hRE hxR))
      refine (convI_eq_one_iff hU ⟨_, hm⟩).1 ?_
      have e2 : (⟨_, hm⟩ : ↥(Subgroup.normalizer (E : Set G))) =
          ⟨y * x * y⁻¹, hyx⟩ * (⟨x, hRE hxR⟩ : ↥(Subgroup.normalizer (E : Set G)))⁻¹ := rfl
      rw [e2, map_mul, map_inv, e, mul_inv_cancel]
    have hyxR : y * x * y⁻¹ ∈ R := by
      have := mul_mem hcomm hxR
      rwa [inv_mul_cancel_right] at this
    refine (hmemP _).mpr ⟨hyxR, ?_⟩
    rw [show (⟨y * x * y⁻¹, hRE hyxR⟩ : ↥(Subgroup.normalizer (E : Set G))) = ⟨_, hyx⟩ from rfl, e]
    exact hxc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf y) := by
    rw [orderOf_eq_prime hy3 hy1]
    decide
  exact hy1 (eq_one_of_normalizes h hMod h63 h1222 h1332 h1334 hF hPR hRP hidx
    (mem_dK_of_odd h h63 hyX hodd) hyP hodd)

end CFSG.Quasithin.H13.L32A
