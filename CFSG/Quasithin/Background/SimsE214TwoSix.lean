module

public import CFSG.Quasithin.Background.SimsE214TwoA
public import CFSG.Quasithin.Background.SimsE210Six
public import CFSG.Quasithin.Background.SimsE213MSp4
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Quasithin.Background.RonanE211Main

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214T

open scoped commutatorElement

section Dihedral

variable {X : Type*} [Group X]

theorem conj_eq_inv_of_mem_zpowers {a b z : X} (ha : a * a = 1) (hb : b * b = 1)
    (hz : z ∈ Subgroup.zpowers (a * b)) : a * z * a⁻¹ = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    rw [MulAut.conj_apply, mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  calc a * (a * b) ^ k * a⁻¹ = MulAut.conj a ((a * b) ^ k) := rfl
    _ = ((a * b) ^ k)⁻¹ := by rw [map_zpow, h1, inv_zpow]

theorem mem_zpowers_or_of_mem_closure {a b x : X} (ha : a * a = 1) (hb : b * b = 1)
    (hx : x ∈ Subgroup.closure {a, b}) :
    x ∈ Subgroup.zpowers (a * b) ∨ x * a ∈ Subgroup.zpowers (a * b) := by
  set Z := Subgroup.zpowers (a * b)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun z hz => by
    rw [conj_eq_inv_of_mem_zpowers ha hb hz]
    exact inv_mem hz
  have hconj' : ∀ z ∈ Z, a⁻¹ * z * a ∈ Z := fun z hz => by
    simpa only [hai] using hconj z hz
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (by rw [ha]; exact one_mem Z)
    · refine Or.inr ?_
      have : x * a = (a * x)⁻¹ := by
        rw [mul_inv_rev, hai, inv_eq_of_mul_eq_one_right hb]
      rw [this]
      exact inv_mem (Subgroup.mem_zpowers _)
  | one => exact Or.inl (one_mem Z)
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have : x * y * a = x * a * (a⁻¹ * y * a) := by group
      rw [this]
      exact mul_mem hx (hconj' y hy)
    · refine Or.inl ?_
      have : x * y = x * a * (a⁻¹ * (y * a) * a) := by
        calc x * y = x * y * (a * a) := by rw [ha, mul_one]
          _ = x * a * (a⁻¹ * (y * a) * a) := by group
      rw [this]
      exact mul_mem hx (hconj' _ hy)
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have : x⁻¹ * a = a * (x * a)⁻¹ * a⁻¹ := by
        rw [mul_inv_rev, hai, ← mul_assoc, ha, one_mul]
      rw [this]
      exact hconj _ (inv_mem hx)

theorem commutator_le_zpowers {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (htop : Subgroup.closure {a, b} = ⊤) : commutator X ≤ Subgroup.zpowers (a * b) := by
  set Z := Subgroup.zpowers (a * b) with hZ
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun z hz => by
    rw [conj_eq_inv_of_mem_zpowers ha hb hz]
    exact inv_mem hz
  have hcomm : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ * z₂ = z₂ * z₁ := by
    intro z₁ hz₁ z₂ hz₂
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₂
    rw [← zpow_add, ← zpow_add, add_comm]
  have hcase : ∀ x : X, ∃ z ∈ Z, x = z ∨ x = z * a := by
    intro x
    rcases mem_zpowers_or_of_mem_closure ha hb (htop ▸ Subgroup.mem_top x) with h | h
    · exact ⟨x, h, Or.inl rfl⟩
    · refine ⟨x * a, h, Or.inr ?_⟩
      rw [mul_assoc, ha, mul_one]
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨z₁, hz₁, hx⟩ := hcase x
  obtain ⟨z₂, hz₂, hy⟩ := hcase y
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · rw [commutatorElement_def, hcomm z₁ hz₁ z₂ hz₂, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem Z
  · have e : ⁅z₁, z₂ * a⁆ = z₁ * z₂ * (a * z₁⁻¹ * a⁻¹) * z₂⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hz₁ hz₂) (hconj _ (inv_mem hz₁))) (inv_mem hz₂)
  · have e : ⁅z₁ * a, z₂⁆ = z₁ * (a * z₂ * a⁻¹) * z₁⁻¹ * z₂⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hz₁ (hconj _ hz₂)) (inv_mem hz₁)) (inv_mem hz₂)
  · have e : ⁅z₁ * a, z₂ * a⁆ = z₁ * (a * (z₂ * z₁⁻¹) * a⁻¹) * z₂⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem hz₁ (hconj _ (mul_mem hz₂ (inv_mem hz₁)))) (inv_mem hz₂)

theorem comm_of_card_two {V₀ : Subgroup X} (hV₀ : Nat.card V₀ = 2)
    (hV₀2 : ∀ v ∈ V₀, v * v = 1) {q : X} (htop : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤)
    {x y : X} (hx : x ∈ commutator X) (hy : y ∈ commutator X) : x * y = y * x := by
  have : Finite V₀ := Nat.finite_of_card_ne_zero (by rw [hV₀]; norm_num)
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ V₀, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 : V₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hno
    rw [h1, Subgroup.card_bot] at hV₀
    exact absurd hV₀ (by norm_num)
  have hVa : V₀ = Subgroup.zpowers a := by
    have hle : Subgroup.zpowers a ≤ V₀ := (Subgroup.zpowers_le).2 ha
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hV₀, Nat.card_zpowers]
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hV₀2 a ha)
    have h3 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact absurd h h3
    · rw [h]
  set b := MulAut.conj q a with hb
  have hb2 : b * b = 1 := by
    rw [hb, ← map_mul, hV₀2 a ha, map_one]
  have htop' : Subgroup.closure {a, b} = ⊤ := by
    rw [← htop, hVa, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
    rfl
  have hc := commutator_le_zpowers (hV₀2 a ha) hb2 htop'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hc hx)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hc hy)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

end Dihedral

theorem not_comm_commutator_perm_six :
    ¬ ∀ x ∈ commutator (Equiv.Perm (Fin 6)), ∀ y ∈ commutator (Equiv.Perm (Fin 6)),
      x * y = y * x := by
  intro h
  have h1 := h _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top (Equiv.swap 0 1))
    (Subgroup.mem_top (Equiv.swap 0 2))) _ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (Equiv.swap 0 1)) (Subgroup.mem_top (Equiv.swap 0 3)))
  revert h1
  decide

variable {G : Type} [Group G] [Finite G]

theorem two_of_six
    (hKG3 : E2.KGI22One) {T M V I : Subgroup G} {g : G}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hsyl : IsSylowTwoOf (T ⊓ I) I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (e : E2.StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6)) :
    (E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I ∧
        E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I))) ∨
      (∃ (_ : ((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I).Normal),
        Nonempty (↥I ⧸ (E2.Pair.PP (M ⊓ I) V I g).subgroupOf I ≃*
          Equiv.Perm (Fin 6) × Multiplicative (ZMod 2)) ∧
        ∀ x : G, x ∈ kerIn (M ⊓ I) I ↔
          x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ E2.Pair.PP (M ⊓ I) V I g) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hp.normal_P
  have hJn := hp.normal_Jbar
  have hJc := hp.Jbar_le_center
  obtain ⟨ρ', hρ'mk, hker, hρ's, hρ'k⟩ := SimsE210.Six.exists_rho hp
  set Xb := E2.Pair.Xbar (M ⊓ I) V I g with hXb
  set Jb := E2.Pair.Jbar (M ⊓ I) V I g with hJb
  set Vb := E2.Pair.Vbar (M ⊓ I) V I g with hVb
  let ρ : Xb →* Equiv.Perm (Fin 6) := e.toMonoidHom.comp ρ'
  have hρs : Function.Surjective ρ := e.surjective.comp hρ's
  have hρk : ρ.ker = Jb := by
    rw [← hρ'k]
    ext x
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  set T₀ : Subgroup Xb :=
    ((T ⊓ I).subgroupOf I).map (E2.Pair.piX (M ⊓ I) V I g) ⊔ Jb with hT₀
  have hVJ : Vb ⊓ Jb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hv, hj⟩
    obtain ⟨⟨v, hvX⟩, hvV, rfl⟩ := hv
    have h1 : ρ' (E2.Pair.piX (M ⊓ I) V I g ⟨v, hvX⟩) = 1 := by
      have : E2.Pair.piX (M ⊓ I) V I g ⟨v, hvX⟩ ∈ ρ'.ker := hρ'k ▸ hj
      exact this
    have h2 : v ∈ kerIn (M ⊓ I) I := Subgroup.mem_subgroupOf.1 ((hker _).1 h1)
    have h3 : v ∈ E2.Pair.PP (M ⊓ I) V I g :=
      Subgroup.mem_sup_left ⟨h2, Subgroup.mem_subgroupOf.1 hvV⟩
    have h4 : (⟨v, hvX⟩ : ↥I) ∈ (E2.Pair.PP (M ⊓ I) V I g).subgroupOf I :=
      Subgroup.mem_subgroupOf.2 h3
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).2 h4
  have hVT' : Vb ≤ T₀ := by
    refine le_trans ?_ le_sup_left
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hTV' : T₀ ≤ Subgroup.normalizer (Vb : Set Xb) := by
    refine sup_le ?_ (hJc.trans (Subgroup.center_le_normalizer _))
    have h1 : ((T ⊓ I).subgroupOf I) ≤
        Subgroup.normalizer ((V.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.1 (hp.normal_T (Subgroup.mem_subgroupOf.1 ht)) (x : G)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  have hcomp : ρ'.comp (E2.Pair.piX (M ⊓ I) V I g) =
      QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) := MonoidHom.ext hρ'mk
  have hmap' : T₀.map ρ' = E2.star (M ⊓ I) I (T ⊓ I) := by
    rw [hT₀, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (le_of_eq hρ'k.symm), sup_bot_eq,
      Subgroup.map_map, hcomp]
    rfl
  have hSyl : IsSylowTwoOf (T₀.map ρ) ⊤ := by
    have : T₀.map ρ = (T₀.map ρ').map e.toMonoidHom := by
      rw [Subgroup.map_map]
    rw [this, hmap']
    exact E2.isSylowTwoOf_map_mulEquiv e (SimsE210.Six.isSylowTwoOf_star_of hp.sylow)
  obtain ⟨-, hcomm0, Y₀, hYinf, hYsup⟩ := SimsE210.Six.six_structure hKG3
    RonanE211.oddCoverExact_perm_six Jb hJc ρ hρs hρk Vb T₀ hp.Vbar_sq hVJ le_sup_right hVT'
    hTV' hSyl hp.top_eq_Vbar_sup_conj.symm
  have hZJ : Subgroup.center Xb = Jb := by
    refine le_antisymm (fun z hz => ?_) hJc
    rw [← hρk, MonoidHom.mem_ker]
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro y
    obtain ⟨x, rfl⟩ := hρs y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  have hJiff := mem_kerIn_iff hp hZJ
  have hVcard : Nat.card Vb = Nat.card (E2.star (M ⊓ I) I V) := by
    obtain ⟨eV⟩ := SimsE210.Six.nonempty_equiv_map_of_inf_ker ρ' Vb (by rw [hρ'k]; exact hVJ)
    have hmV : Vb.map ρ' = E2.star (M ⊓ I) I V := by
      rw [hVb, Subgroup.map_map, hcomp]
      rfl
    rw [Nat.card_congr eV.toEquiv, hmV]
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  have hY6 : IsSp4Full 1 (E2.StarQuot (M ⊓ I) I) := Or.inr ⟨rfl, ⟨e⟩⟩
  have hZ4 : Nat.card ↥(centerOf (E2.star (M ⊓ I) I (T ⊓ I))) ≤ 4 :=
    E213M.card_le_of_le_centralizer hY6 hS inf_le_left inf_le_right
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hV4 : Nat.card ↥(E2.star (M ⊓ I) I V) ≤ 4 :=
    E213M.card_le_of_le_centralizer hY6 hS hVT hVZ
  have hV2 : IsPGroup 2 Vb := fun x =>
    ⟨1, Subtype.ext (by
      rw [SubmonoidClass.coe_pow, pow_one, pow_two, OneMemClass.coe_one]
      exact hp.Vbar_sq _ x.2)⟩
  have : Nontrivial (E2.StarQuot (M ⊓ I) I) := e.toEquiv.nontrivial
  have hV1 : Nat.card Vb ≠ 1 := by
    intro h1
    apply E2.star_ne_bot_of_gen hg hgen (M' := M ⊓ I)
    rw [← Subgroup.card_eq_one, ← hVcard, h1]
  have hVne2 : Nat.card Vb ≠ 2 := by
    intro h2
    apply not_comm_commutator_perm_six
    have hmapc : (commutator Xb).map ρ = commutator (Equiv.Perm (Fin 6)) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ρ hρs]
    intro x hx y hy
    rw [← hmapc] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, comm_of_card_two h2 hp.Vbar_sq hp.top_eq_Vbar_sup_conj.symm hx' hy']
  have hV4' : 4 ≤ Nat.card Vb := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
    rw [hn] at hV1 hVne2 ⊢
    rcases n with _ | _ | n
    · exact absurd rfl hV1
    · exact absurd rfl hVne2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set L := commutator Xb with hL
  have hLcard : Nat.card L = 360 := by
    obtain ⟨eL⟩ := SimsE210.Six.nonempty_commutator_equiv ρ hρs (by rw [hρk]; exact hcomm0)
    rw [Nat.card_congr eL.toEquiv, alternatingGroup.commutator_perm_eq (by simp),
      nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hLidx : L.index ≤ Nat.card Vb := by
    have h1 : L.index = L.relIndex Vb := by
      rw [← Subgroup.relIndex_top_right, hp.top_eq_commutator_sup_Vbar, sup_comm,
        Subgroup.relIndex_sup_right]
    rw [h1]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card L Vb)
  have hXcard : Nat.card Xb = 720 * Nat.card Jb := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Jb,
      Nat.card_congr hp.quotJbarEquiv.toEquiv, Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hJ2 : Nat.card Jb ≤ 2 := by
    have h1 := Subgroup.index_mul_card L
    rw [hLcard, hXcard] at h1
    have h2 : L.index ≤ 4 := hLidx.trans (hVcard ▸ hV4)
    omega
  have hJpos : 0 < Nat.card Jb := Nat.card_pos
  rcases (show Nat.card Jb = 1 ∨ Nat.card Jb = 2 by omega) with hJ1 | hJ2'
  ·
    left
    have hJbot : Jb = ⊥ := Subgroup.eq_bot_of_card_eq Jb hJ1
    refine ⟨le_antisymm hp.P_le_J fun j hj => ?_, ?_⟩
    · have hjI : j ∈ I := kerIn_le.trans hp.le_X hj
      have h1 : QuotientGroup.mk' ((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I) (⟨j, hjI⟩ : I) ∈ Jb :=
        ⟨⟨j, hjI⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      rw [hJbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h1
      exact h1
    · refine Subgroup.eq_of_le_of_card_ge (le_inf hVT hVZ) ?_
      rw [← hVcard]
      exact hZ4.trans hV4'
  ·
    right
    obtain ⟨eY⟩ := SimsE210.Six.nonempty_equiv_of_compl ρ hρs Y₀ (by rw [hρk]; exact hYinf)
      (by rw [hρk]; exact hYsup)
    have eJ : ↥Jb ≃* Multiplicative (ZMod 2) :=
      mulEquivOfPrimeCardEq hJ2' (by rw [Nat.card_eq_fintype_card]; rfl)
    let φ : ↥Y₀ × ↥Jb →* Xb := MonoidHom.noncommCoprod Y₀.subtype Jb.subtype fun m n =>
      (Subgroup.mem_center_iff.mp (hJc n.2) (m : Xb))
    have hφ : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_one φ).2 fun ⟨m, n⟩ h1 => ?_, fun x => ?_⟩
      · have h1' : (m : Xb) * (n : Xb) = 1 := h1
        have hmn : (m : Xb) = (n : Xb)⁻¹ := eq_inv_of_mul_eq_one_left h1'
        have hmJ : (m : Xb) ∈ Y₀ ⊓ Jb := ⟨m.2, hmn ▸ Jb.inv_mem n.2⟩
        rw [hYinf, Subgroup.mem_bot] at hmJ
        have hn1 : (n : Xb) = 1 := by rw [← inv_inj, ← hmn, hmJ, inv_one]
        exact Prod.ext (Subtype.ext hmJ) (Subtype.ext hn1)
      · have hx : x ∈ Y₀ ⊔ Jb := hYsup ▸ Subgroup.mem_top x
        obtain ⟨y, hy, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
        exact ⟨(⟨y, hy⟩, ⟨j, hj⟩), rfl⟩
    exact ⟨hp.normal_P, ⟨(MulEquiv.ofBijective φ hφ).symm.trans (MulEquiv.prodCongr eY eJ)⟩,
      hJiff⟩

end E214T

end CFSG.Quasithin.SimsE2
