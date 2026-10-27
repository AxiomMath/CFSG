module

public import CFSG.Quasithin.H13.A6S13820Aut1
public import CFSG.Quasithin.H13.A6S13821zh
public import CFSG.Quasithin.H13.A6S13821z

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Aut20

theorem le_of_isSylowTwoOf_top20 {G : Type} [Group G] [Finite G] {S M : Subgroup G}
    (hS : IsSylowTwoOf S ⊤) (hM : IsPGroup 2 M) (hSM : S ≤ M) : M ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex S M ⊤ hSM le_top
  have hodd : ¬ 2 ∣ S.relIndex M := fun h =>
    hS.2.2 (by
      have : S.relIndex ⊤ = (S.subgroupOf ⊤).index := rfl
      rw [← this, ← h1]
      exact h.mul_right _)
  have hidx : S.relIndex M = 1 := by
    obtain ⟨n, hn⟩ := hM.index (S.subgroupOf M)
    have hn' : S.relIndex M = 2 ^ n := hn
    rcases n with _ | n
    · simpa using hn'
    · exact absurd (hn' ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)) hodd
  exact Subgroup.relIndex_eq_one.mp hidx

theorem key_K4_20 : ∀ π : Perm (Fin 6), π 4 = 4 → π 5 = 5 → Perm.sign π = 1 →
    (swap 0 1 * swap 4 5) * π * (swap 0 1 * swap 4 5)⁻¹ * π ∈ K4L := by
  decide +kernel

theorem dvd_three_of_odd20 {d : ℕ} (h48 : d ∣ 48) (hodd : ¬ 2 ∣ d) : d ∣ 3 := by
  have hcop : Nat.Coprime d 16 :=
    Nat.Coprime.pow_right 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  exact hcop.dvd_of_dvd_mul_left (by simpa using h48)

@[expose] def borel20 {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)

@[expose] def borelC20 {G : Type} [Group G] (T K V : Subgroup G) : Subgroup G :=
  (borel20 T K ⊓ Subgroup.centralizer (V : Set G)) ⊔ (T ⊓ K)

end Aut20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_t20 :
    ∃ t ∈ T ⊓ L, ∀ x ∈ S.X13820, t * x * t⁻¹ * x ∈ pCoreOf 2 S.X13820 := by
  have P := S.plusData_X13820
  obtain ⟨hD, hs, -⟩ := S14.t0_facts
  obtain ⟨t, htTL, hρt⟩ := S14.exists_TL_rho S hD hs
  refine ⟨t, htTL, fun x hx => ?_⟩
  have hxN := P.le_NV hx
  have hy : (t : G) * x * (t : G)⁻¹ * x ∈ S.X13820 :=
    S.X13820.mul_mem ((Subgroup.mem_normalizer_iff.mp (P.T_le htTL.1) x).mp hx) hx
  obtain ⟨h4, h5, hsg⟩ := P.rho (x := ⟨x, hxN⟩) hx
  have hρ : S.frame.ρ (t * ⟨x, hxN⟩ * t⁻¹ * ⟨x, hxN⟩) ∈ K4L := by
    rw [map_mul, map_mul, map_mul, map_inv, hρt]
    exact Aut20.key_K4_20 _ h4 h5 hsg
  exact P.mem_pCoreOf_of_K4 (x := t * ⟨x, hxN⟩ * t⁻¹ * ⟨x, hxN⟩) hy hρ

theorem pCoreOf_L_le_T20 : pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top
  have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 L) :=
    hTs.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 L)
      (S.T_le_NL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  exact le_sup_right.trans (Aut20.le_of_isSylowTwoOf_top20 hTs hsup le_sup_left)

theorem comm_mem_inf20 {c : G} (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcV : c ∈ Subgroup.centralizer (V : Set G)) {l : G} (hl : l ∈ L) :
    l⁻¹ * (c⁻¹ * l * c) ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
  have hc' : c⁻¹ * l * c ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcL) l).mp hl
    simpa using this
  refine ⟨L.mul_mem (L.inv_mem hl) hc', ?_⟩
  show l⁻¹ * (c⁻¹ * l * c) ∈ Subgroup.centralizer (V : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) v).mp hv
  have hcv : v * c = c * v := Subgroup.mem_centralizer_iff.mp hcV v hv
  have hcv' : (l * v * l⁻¹) * c = c * (l * v * l⁻¹) := Subgroup.mem_centralizer_iff.mp hcV _ hv'
  have hcv'' : c⁻¹ * (l * v * l⁻¹) = (l * v * l⁻¹) * c⁻¹ := by
    calc c⁻¹ * (l * v * l⁻¹) = c⁻¹ * ((l * v * l⁻¹) * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (l * v * l⁻¹)) * c⁻¹ := by rw [hcv']
      _ = (l * v * l⁻¹) * c⁻¹ := by group
  symm
  calc l⁻¹ * (c⁻¹ * l * c) * v = l⁻¹ * c⁻¹ * l * (c * v) := by group
    _ = l⁻¹ * c⁻¹ * l * (v * c) := by rw [hcv]
    _ = l⁻¹ * (c⁻¹ * (l * v * l⁻¹)) * l * c := by group
    _ = l⁻¹ * ((l * v * l⁻¹) * c⁻¹) * l * c := by rw [hcv'']
    _ = v * (l⁻¹ * (c⁻¹ * l * c)) := by group

theorem comm_mem_pCoreOf20 {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcV : c ∈ Subgroup.centralizer (V : Set G))
    {l : G} (hl : l ∈ L) : l⁻¹ * (c⁻¹ * l * c) ∈ pCoreOf 2 L := by
  have := S.perfect_Q
  set τ := Aut20.act20 L ⟨c⁻¹, Subgroup.inv_mem _ hcL⟩ with hτ
  have hτ1 : τ = 1 := by
    refine Aut20.eq_one_of_perfect20 fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [hτ, Aut20.act20_mk]
      obtain ⟨w, hw, hwe⟩ := S.centralizer_le_o2Z (S.comm_mem_inf20 hcL hcV y.2)
      have e : y⁻¹ * (⟨c⁻¹ * y * c⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ hcL) y).mp y.2⟩ : ↥L) = w := by
        apply Subtype.ext
        change _ = L.subtype w
        rw [hwe]
        simp
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, e]
      exact hw
  have h1 := congrArg (fun φ : MulAut (ModO2 L) => φ ((⟨l, hl⟩ : ↥L) : ModO2 L)) hτ1
  simp only [hτ, Aut20.act20_mk, MulAut.one_apply] at h1
  have h2 := (QuotientGroup.eq (s := CFSG.pCore 2 ↥L)).1 h1.symm
  rw [← pCoreOf_subgroupOf_eq L] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa using h3

theorem borel20_facts (h1334 : Stmt13_3_4) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hB : Aut20.borel20 T K ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T ⊓ L) :
    Aut20.borelC20 T K V ≤ Aut20.borel20 T K ∧
      (∀ b ∈ Aut20.borel20 T K, ∀ c ∈ Aut20.borelC20 T K V, b * c * b⁻¹ ∈ Aut20.borelC20 T K V) ∧
      (Aut20.borelC20 T K V).relIndex (Aut20.borel20 T K) ∣ 3 ∧
      ∀ c ∈ Aut20.borelC20 T K V, c⁻¹ * (t * c * t⁻¹) ∈ T ⊓ K := by
  set B := Aut20.borel20 T K with hBdef
  set C := Aut20.borelC20 T K V with hCdef
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hBH : B ≤ H := inf_le_left.trans hKH
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := fun b hb =>
    S.inf_M_le_NV h1334 hH ⟨hBH hb, hB hb⟩
  have hTKB : T ⊓ K ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  have hCB : C ≤ B := sup_le inf_le_left hTKB
  have hnorm : ∀ b ∈ B, ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb
    have hle : C ≤ C.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun p hp => ?_)
      · show b * a * b⁻¹ ∈ C
        refine Subgroup.mem_sup_left ⟨B.mul_mem (B.mul_mem hb ha.1) (B.inv_mem hb), ?_⟩
        show b * a * b⁻¹ ∈ Subgroup.centralizer (V : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hv' : b⁻¹ * v * b ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBV hb)) v).mp hv
          simpa using this
        have hav := Subgroup.mem_centralizer_iff.mp ha.2 _ hv'
        calc v * (b * a * b⁻¹) = b * ((b⁻¹ * v * b) * a) * b⁻¹ := by group
          _ = b * (a * (b⁻¹ * v * b)) * b⁻¹ := by rw [hav]
          _ = b * a * b⁻¹ * v := by group
      · show b * p * b⁻¹ ∈ C
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hb.2 p).mp hp)
    exact fun c hc => hle hc
  refine ⟨hCB, hnorm, ?_, ?_⟩
  ·
    set ψ : ↥B →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hBV) with hψ
    have hker : ψ.ker = (B ⊓ Subgroup.centralizer (V : Set G)).subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
        S.rho_eq_one_iff]
      exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
    have hrange : ψ.range ≤ L2Case.stabZ := by
      rintro _ ⟨b, rfl⟩
      have hb1 : (b : G) ∈ S.G1 := hH.2.1 (hBH b.2)
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at hb1
      exact S.fix_e0123 _ (by show (b : G) * S.z * (b : G)⁻¹ = S.z; rw [hb1, mul_inv_cancel_right])
    have h48 : (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B ∣ 48 := by
      have hidx : (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B = Nat.card ψ.range := by
        show ((B ⊓ Subgroup.centralizer (V : Set G)).subgroupOf B).index = _
        rw [← hker, Subgroup.index_ker]
      rw [hidx, ← L2Case.card_stabZ]
      exact Subgroup.card_dvd_of_le hrange
    have hdvd1 : C.relIndex B ∣ (B ⊓ Subgroup.centralizer (V : Set G)).relIndex B :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ C B le_sup_left hCB)
    have hodd : ¬ 2 ∣ C.relIndex B := by
      intro h2
      have hsyl := S.isSylowTwoOf_TK hH hKH hKn
      have h1 : C.relIndex B ∣ (T ⊓ K).relIndex B :=
        Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ C B le_sup_right hCB)
      have h3 : (T ⊓ K).relIndex B ∣ (T ⊓ K).relIndex K :=
        Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ B K hTKB inf_le_left)
      exact hsyl.2.2 ((h2.trans h1).trans h3)
    exact Aut20.dvd_three_of_odd20 (hdvd1.trans h48) hodd
  ·
    have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht.1)) k).mp hk
    let D : Subgroup G :=
      { carrier := {c | c ∈ B ∧ c⁻¹ * (t * c * t⁻¹) ∈ T ⊓ K}
        mul_mem' := by
          rintro a b ⟨haB, ha⟩ ⟨hbB, hb⟩
          refine ⟨B.mul_mem haB hbB, ?_⟩
          have e : (a * b)⁻¹ * (t * (a * b) * t⁻¹) =
              (b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * b) * (b⁻¹ * (t * b * t⁻¹)) := by group
          rw [e]
          refine (T ⊓ K).mul_mem ?_ hb
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbB.2) _).mp ha
          simpa using this
        one_mem' := ⟨B.one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨haB, ha⟩
          refine ⟨B.inv_mem haB, ?_⟩
          have e : a⁻¹⁻¹ * (t * a⁻¹ * t⁻¹) = a * (a⁻¹ * (t * a * t⁻¹))⁻¹ * a⁻¹ := by group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp haB.2 _).mp ((T ⊓ K).inv_mem ha) }
    have hCD : C ≤ D := by
      refine sup_le (fun c hc => ⟨hc.1, ?_, ?_⟩) (fun c hc => ⟨hTKB hc, ?_, ?_⟩)
      · have h1 := S.comm_mem_pCoreOf20 (hB hc.1) hc.2 ht.2
        have h2 : t⁻¹ * (c⁻¹ * t * c) ∈ T := S.pCoreOf_L_le_T20 h1
        have e : c⁻¹ * (t * c * t⁻¹) = t * (t⁻¹ * (c⁻¹ * t * c)) * t⁻¹ := by group
        rw [e]
        exact T.mul_mem (T.mul_mem ht.1 h2) (T.inv_mem ht.1)
      · exact K.mul_mem (K.inv_mem hc.1.1) (htK _ hc.1.1)
      · exact T.mul_mem (T.inv_mem hc.1) (T.mul_mem (T.mul_mem ht.1 hc.1) (T.inv_mem ht.1))
      · exact K.mul_mem (K.inv_mem hc.2) (htK _ hc.2)
    exact fun c hc => (hCD hc).2

end Setting4

end CFSG.Quasithin.H13.A6
