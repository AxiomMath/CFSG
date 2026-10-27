module

public import CFSG.Quasithin.Background.SmithB45LnL5Comm
public import CFSG.Quasithin.Background.SmithB42LnL5Dim
public import CFSG.Quasithin.Background.SmithB42LnL5Case11
public import CFSG.Quasithin.Background.SmithB45G2Base
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import Certificates.Certificate8026Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.B42Ln CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis

namespace B45L5

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

section Index

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))}

theorem card_fixV_le_of_le {B : Subgroup (MulAut V)} {K : Submodule (ZMod 2) (Additive V)}
    (hK : ∀ v ∈ fixV B, Additive.ofMul v ∈ K) :
    Nat.card (fixV B) ≤ 2 ^ Module.finrank (ZMod 2) K := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have h1 : Nat.card (fixV B) ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective (fun v => ⟨Additive.ofMul v.1, hK v.1 v.2⟩) ?_
    intro v w h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Additive.ofMul.injective h')
  rwa [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K), Nat.card_zmod] at h1

omit [Finite V] in
theorem mem_ker_of_mem {B : Subgroup (MulAut V)} {x : G5} (hx : fL e x ∈ B) {v : V}
    (hv : v ∈ fixV B) : Additive.ofMul v ∈ LinearMap.ker (repOf (phiOf e) x - 1) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, repOf_apply,
    ← fL_apply, hv _ hx]

theorem pow_le_index_of_le {B : Subgroup (MulAut V)} {K : Submodule (ZMod 2) (Additive V)}
    (hK : ∀ v ∈ fixV B, Additive.ofMul v ∈ K) :
    2 ^ (Module.finrank (ZMod 2) (Additive V) - Module.finrank (ZMod 2) K) ≤ (fixV B).index := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have h1 := card_fixV_le_of_le hK
  have h2 := (fixV B).index_mul_card
  rw [card_eq_two_pow_finrank (V := V)] at h2
  have h3 : Module.finrank (ZMod 2) K ≤ Module.finrank (ZMod 2) (Additive V) :=
    Submodule.finrank_le K
  have h4 : 2 ^ (Module.finrank (ZMod 2) (Additive V) - Module.finrank (ZMod 2) K) *
      2 ^ Module.finrank (ZMod 2) K = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [← pow_add, Nat.sub_add_cancel h3]
  have h5 : 2 ^ (Module.finrank (ZMod 2) (Additive V) - Module.finrank (ZMod 2) K) *
      2 ^ Module.finrank (ZMod 2) K ≤ (fixV B).index * 2 ^ Module.finrank (ZMod 2) K := by
    rw [h4, ← h2]
    exact Nat.mul_le_mul_left _ h1
  exact Nat.le_of_mul_le_mul_right h5 (by positivity)

theorem pow_le_index_of_mem {B : Subgroup (MulAut V)} {x : G5} (hx : fL e x ∈ B) :
    2 ^ Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1)) ≤ (fixV B).index := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have h := pow_le_index_of_le (K := LinearMap.ker (repOf (phiOf e) x - 1))
    fun v hv => mem_ker_of_mem hx hv
  have h2 := LinearMap.finrank_range_add_finrank_ker (repOf (phiOf e) x - 1)
  rwa [show Module.finrank (ZMod 2) (Additive V) -
      Module.finrank (ZMod 2) (LinearMap.ker (repOf (phiOf e) x - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1)) by omega] at h

end Index

theorem exists_inv_of_outer5 (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {a₀ : MulAut V} (ha₀G : a₀ ∈ G) (ha₀L : a₀ ∉ L)
    (ha₀2 : a₀ * a₀ = 1) :
    ∃ x : G5, x * x = 1 ∧ x ≠ 1 ∧
      (fixV (Subgroup.zpowers (fL e x))).index ≤ (fixV (Subgroup.zpowers a₀)).index ^ 2 := by
  obtain ⟨P, hP⟩ := exists_conjG5_eq hHyp hZ e ha₀G ha₀L
  have hPs := transpose_P hHyp e ha₀G ha₀2 hP
  obtain ⟨γ, hγ2, hx1, hx2⟩ := exists_conj_mul_inv hPs hP
  refine ⟨conjG5 hHyp e ha₀G γ * γ, hx2, hx1, ?_⟩
  set γ' := fL e γ with hγ'
  have hγ'inv : γ'⁻¹ = γ' := by
    rw [hγ', ← map_inv, inv_eq_of_mul_eq_one_right hγ2]
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
  have hxeq : fL e (conjG5 hHyp e ha₀G γ * γ) = a₀ * (γ' * a₀ * γ'⁻¹) := by
    rw [map_mul, fL_apply, conjG5_spec, ← fL_apply, ← hγ', hγ'inv, ha₀inv]
    group
  set B : Fin 2 → Subgroup (MulAut V) :=
    ![Subgroup.zpowers a₀, (Subgroup.zpowers a₀).map (MulAut.conj γ').toMonoidHom] with hB
  have hle : Subgroup.zpowers (fL e (conjG5 hHyp e ha₀G γ * γ)) ≤ ⨆ i, B i := by
    rw [Subgroup.zpowers_le, hxeq]
    refine Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_zpowers a₀))
      (Subgroup.mem_iSup_of_mem 1 ⟨a₀, Subgroup.mem_zpowers a₀, ?_⟩)
    show (MulAut.conj γ') a₀ = _
    rw [MulAut.conj_apply]
  have h1 := index_fixV_le_prod B hle
  rw [Fin.prod_univ_two] at h1
  have hB1 : (fixV (B 1)).index = (fixV (B 0)).index :=
    CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
  rw [hB1] at h1
  calc _ ≤ (fixV (B 0)).index * (fixV (B 0)).index := h1
    _ = (fixV (Subgroup.zpowers a₀)).index ^ 2 := (sq _).symm

theorem card_le_64 (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hAG : A ≤ G) (hel : IsElemAbelian2 A) :
    Nat.card A ≤ 64 := by
  have hcS := comm_of_comap (e := e) hel
  have h2S := sq_of_comap (e := e) hel
  by_cases hAL : A ≤ L
  · rw [← card_comap_eq e hAL]
    exact card_le_of_elemAbelian hcS h2S
  · obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    obtain ⟨P, hP⟩ := exists_conjG5_eq hHyp hZ e (hAG ha₀) ha₀L
    have h32 := card_le_32_of_fixed hP hcS h2S (conjG5_fix hHyp e hel ha₀ (hAG ha₀))
    have := card_le_two_mul_comap hHyp hZ e hAG
    omega

theorem exists_inv_of_comap_eq_bot (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hA : IsA2 G A)
    (h2F : (fixV A).index ≤ Nat.card A ^ 2) (hS : A.comap (fL e) = ⊥) :
    ∃ x : G5, x * x = 1 ∧ x ≠ 1 ∧ (fixV (Subgroup.zpowers (fL e x))).index ≤ 16 := by
  have hAL : ¬ A ≤ L := by
    intro hAL
    apply hA.2.1
    have h1 := card_comap_eq e hAL
    rw [hS, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
  have hA2 : Nat.card A ≤ 2 := by
    have := card_le_two_mul_comap hHyp hZ e hA.1
    rw [hS, Subgroup.card_bot] at this
    omega
  have ha₀2 : a₀ * a₀ = 1 := by rw [← pow_two]; exact hA.2.2.2 a₀ ha₀
  obtain ⟨x, hx2, hx1, hxi⟩ := exists_inv_of_outer5 hHyp hZ e (hA.1 ha₀) ha₀L ha₀2
  have hB0 : (fixV (Subgroup.zpowers a₀)).index ≤ 4 := by
    refine (index_fixV_mono ((Subgroup.zpowers_le).2 ha₀)).trans (h2F.trans ?_)
    calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hA2 2
      _ = 4 := by norm_num
  exact ⟨x, hx2, hx1, hxi.trans ((Nat.pow_le_pow_left hB0 2).trans (by norm_num))⟩

section Disp

variable [Module (ZMod 2) (Additive V)]

theorem false_of_disp (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hA : IsA2 G A)
    (h2F : (fixV A).index ≤ Nat.card A ^ 2)
    (hdisp : ∀ x : G5, x * x = 1 → x ≠ 1 →
      13 ≤ Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1))) : False := by
  have h64 := card_le_64 hHyp hZ e hA.1 hA.2.2
  by_cases hS : A.comap (fL e) = ⊥
  · obtain ⟨x, hx2, hx1, hx16⟩ := exists_inv_of_comap_eq_bot hHyp hZ e hA h2F hS
    have h1 := pow_le_index_of_mem (e := e) (Subgroup.mem_zpowers (fL e x))
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hdisp x hx2 hx1)
    have : (16 : ℕ) < 2 ^ 13 := by norm_num
    omega
  · obtain ⟨⟨b, hbS⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
    have hb1' : b ≠ 1 := fun h0 => hb1 (by subst h0; rfl)
    have h1 := pow_le_index_of_mem (e := e) (B := A) hbS
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (hdisp b (sq_of_comap (e := e) hA.2.2 b hbS) hb1')
    have h3 : Nat.card A ^ 2 ≤ 64 ^ 2 := Nat.pow_le_pow_left h64 2
    have : (64 : ℕ) ^ 2 < 2 ^ 13 := by norm_num
    omega

end Disp

section Adj

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))}
  {β : Additive V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)}

theorem le_finrank_adj (hβ : ∀ g v, β (repOf (phiOf e) g v) = rep24 g (β v)) {x : G5}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1)) ∧
      (∀ c : G5, c * x * c⁻¹ = B42Ln.s0 →
        12 ≤ Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1))) := by
  have hn : Module.finrank (ZMod 2) (Additive V) = 24 := by
    rw [β.finrank_eq, Module.finrank_fin_fun]
  have h3 := LinearMap.finrank_range_add_finrank_ker (repOf (phiOf e) x - 1)
  have hs : ∀ c : G5, c * x * c⁻¹ = B42Ln.s0 →
      12 ≤ Module.finrank (ZMod 2) (LinearMap.range (repOf (phiOf e) x - 1)) := by
    intro c hc
    have h1 := finrank_ker_eq hβ c x
    rw [hc] at h1
    have h2 := finrank_fix_s0
    omega
  refine ⟨?_, hs⟩
  obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 hx2 hx1
  · have h1 := finrank_ker_eq hβ c x
    rw [hc] at h1
    have h2 := finrank_fix_t0
    omega
  · have := hs c hc
    omega

omit [Finite V] in
theorem finrank_pair_adj (hβ : ∀ g v, β (repOf (phiOf e) g v) = rep24 g (β v)) {a b : G5}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hab : a * b = b * a) (hb1 : b ≠ 1) (hba : b ≠ a) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) a - 1) ⊓
        LinearMap.ker (repOf (phiOf e) b - 1)) ≤ 15 ∧
      (∀ c : G5, c * a * c⁻¹ = B42Ln.s0 →
        Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) a - 1) ⊓
          LinearMap.ker (repOf (phiOf e) b - 1)) ≤ 11) := by
  have hconj : ∀ c : G5, (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) ∧
      c * b * c⁻¹ ≠ 1 ∧ c * b * c⁻¹ ≠ c * a * c⁻¹ := by
    intro c
    refine ⟨by rw [show c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ by group, hab]; group,
      fun h => hb1 ?_, fun h => hba ?_⟩
    · calc b = c⁻¹ * (c * b * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · calc b = c⁻¹ * (c * b * c⁻¹) * c := by group
        _ = c⁻¹ * (c * a * c⁻¹) * c := by rw [h]
        _ = a := by group
  have hs : ∀ c : G5, c * a * c⁻¹ = B42Ln.s0 →
      Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) a - 1) ⊓
        LinearMap.ker (repOf (phiOf e) b - 1)) ≤ 11 := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hconj c
    rw [finrank_ker_inf_eq hβ c a b, hc]
    rw [hc] at h1 h3
    exact finrank_fix_pair_s0 h1 h2 h3
  refine ⟨?_, hs⟩
  obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 ha2 ha1
  · obtain ⟨h1, h2, h3⟩ := hconj c
    rw [finrank_ker_inf_eq hβ c a b, hc]
    rw [hc] at h1 h3
    exact finrank_fix_pair_t0 h1 h2 h3
  · have := hs c hc
    omega

theorem pow_le_index_pair {a b : G5} (ha : fL e a ∈ A) (hb : fL e b ∈ A) :
    2 ^ (Module.finrank (ZMod 2) (Additive V) -
      Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) a - 1) ⊓
        LinearMap.ker (repOf (phiOf e) b - 1))) ≤ (fixV A).index :=
  pow_le_index_of_le fun _ hv => ⟨mem_ker_of_mem ha hv, mem_ker_of_mem hb hv⟩

theorem exists_third {S : Subgroup G5} (h2S : ∀ s ∈ S, s * s = 1) (hS : 2 < Nat.card S)
    {a : G5} : ∃ b ∈ S, b ≠ 1 ∧ b ≠ a := by
  classical
  by_contra h
  push Not at h
  by_cases haS : a ∈ S
  · have hle : S ≤ Subgroup.zpowers a := by
      intro b hb
      by_cases hb1 : b = 1
      · rw [hb1]
        exact Subgroup.one_mem _
      · rw [h b hb hb1]
        exact Subgroup.mem_zpowers a
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf a ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact h2S a haS)
    omega
  · have hle : S ≤ ⊥ := by
      intro b hb
      rw [Subgroup.mem_bot]
      by_contra hb1
      exact haS (h b hb hb1 ▸ hb)
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at h1
    omega

theorem false_of_adj (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hβ : ∀ g v, β (repOf (phiOf e) g v) = rep24 g (β v)) (hA : IsA2 G A)
    (h2F : (fixV A).index ≤ Nat.card A ^ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : Module.finrank (ZMod 2) (Additive V) = 24 := by
    rw [β.finrank_eq, Module.finrank_fin_fun]
  have hAG : A ≤ G := hA.1
  have hel : IsElemAbelian2 A := hA.2.2
  have hcS := comm_of_comap (e := e) hel
  have h2S := sq_of_comap (e := e) hel
  have h64 := card_le_64 hHyp hZ e hAG hel
  set S := A.comap (fL e) with hSdef
  by_cases hS : S = ⊥
  · obtain ⟨x, hx2, hx1, hx16⟩ := exists_inv_of_comap_eq_bot hHyp hZ e hA h2F hS
    have h1 := pow_le_index_of_mem (e := e) (Subgroup.mem_zpowers (fL e x))
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_finrank_adj hβ hx2 hx1).1
    have : (16 : ℕ) < 2 ^ 8 := by norm_num
    omega
  obtain ⟨⟨b₁, hb₁S⟩, hb₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
  have hb₁1' : b₁ ≠ 1 := fun h0 => hb₁1 (by subst h0; rfl)
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S).exists_card_eq
  have hcardA : Nat.card A ≤ 2 * Nat.card S := card_le_two_mul_comap hHyp hZ e hAG
  by_cases hk1 : k ≤ 1
  · have hS2 : Nat.card S ≤ 2 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    have hA4 : Nat.card A ≤ 4 := by omega
    have h1 := pow_le_index_of_mem (e := e) (B := A) hb₁S
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (le_finrank_adj hβ (h2S b₁ hb₁S) hb₁1').1
    have h3 : Nat.card A ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hA4 2
    have : (4 : ℕ) ^ 2 < 2 ^ 8 := by norm_num
    omega
  have hS4 : 2 < Nat.card S := by
    rw [hk]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hs0 : ∃ a ∈ S, ∃ c : G5, c * a * c⁻¹ = B42Ln.s0
  ·
    obtain ⟨a, haS, c, hc⟩ := hs0
    have ha1 : a ≠ 1 := by
      rintro rfl
      apply sB0_ne.1
      rw [← coe_s0, ← hc, mul_one, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨b, hbS, hb1, hba⟩ := exists_third h2S hS4 (a := a)
    have h1 := pow_le_index_pair (e := e) haS hbS
    have h2 := (finrank_pair_adj hβ (h2S a haS) ha1 (hcS a haS b hbS) hb1 hba).2 c hc
    have h3 : 2 ^ 13 ≤ 2 ^ (Module.finrank (ZMod 2) (Additive V) -
        Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) a - 1) ⊓
          LinearMap.ker (repOf (phiOf e) b - 1))) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : Nat.card A ^ 2 ≤ 64 ^ 2 := Nat.pow_le_pow_left h64 2
    have : (64 : ℕ) ^ 2 < 2 ^ 13 := by norm_num
    omega
  push Not at hs0
  have hT : ∀ s ∈ S, s ≠ 1 → ∃ v ψ, IsTv s v ψ := by
    intro s hs hs1
    obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 (h2S s hs) hs1
    · have h := isTv_conj_t0 c⁻¹
      have e1 : c⁻¹ * t0 * c⁻¹⁻¹ = s := by rw [← hc]; group
      rw [e1] at h
      exact ⟨_, _, h⟩
    · exact absurd hc (hs0 s hs c)
  have hS16 : Nat.card S ≤ 16 := by
    rcases common_center_or_axis hcS h2S hT with ⟨v, hv⟩ | ⟨ψ, hψ⟩
    · have hv0 : v ≠ 0 := by
        obtain ⟨ψ, hψ⟩ := hv b₁ hb₁S hb₁1'
        exact hψ.2.1
      exact (card_le_of_center hv0 hv).1
    · have hψ0 : ψ ≠ 0 := by
        obtain ⟨v, hv⟩ := hψ b₁ hb₁S hb₁1'
        exact hv.2.2.1
      exact (card_le_of_axis hψ0 hψ).1
  have hAL : A ≤ L := by
    by_contra hAL
    obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    obtain ⟨P, hP⟩ := exists_conjG5_eq hHyp hZ e (hAG ha₀) ha₀L
    have hfix := conjG5_fix hHyp e hel ha₀ (hAG ha₀)
    have hS2 : Nat.card S ≤ 2 := by
      rcases common_center_or_axis hcS h2S hT with ⟨v, hv⟩ | ⟨ψ, hψ⟩
      · exact card_le_two_of_center hP hfix hv
      · exact card_le_two_of_axis hP hfix hψ
    omega
  have hA16 : Nat.card A ≤ 16 := by
    rw [← card_comap_eq e hAL]
    exact hS16
  obtain ⟨b, hbS, hb1, hbb₁⟩ := exists_third h2S hS4 (a := b₁)
  have h1 := pow_le_index_pair (e := e) hb₁S hbS
  have h2 := (finrank_pair_adj hβ (h2S b₁ hb₁S) hb₁1' (hcS b₁ hb₁S b hbS) hb1 hbb₁).1
  have h3 : 2 ^ 9 ≤ 2 ^ (Module.finrank (ZMod 2) (Additive V) -
      Module.finrank (ZMod 2) ↥(LinearMap.ker (repOf (phiOf e) b₁ - 1) ⊓
        LinearMap.ker (repOf (phiOf e) b - 1))) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : Nat.card A ^ 2 ≤ 16 ^ 2 := Nat.pow_le_pow_left hA16 2
  have : (16 : ℕ) ^ 2 < 2 ^ 9 := by norm_num
  omega

end Adj

section FF

variable [Module (ZMod 2) (Additive V)]

theorem qhatOf_le_one_of_sub5 (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ' : Representation (ZMod 2) G5 W) (κ : G5 ≃* G5) (β : Additive V ≃ₗ[ZMod 2] W)
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = ρ' (κ g) (β w)) (Y : Subgroup G5)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ a ∈ Y, a * a = 1) (hY1 : Y ≠ ⊥)
    (hcard : Nat.card W ≤ Nat.card Y * Nat.card {x : W // ∀ u ∈ Y, ρ' u x = x}) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, hLF, -, -⟩ := hHyp
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  let ι : G5 →* MulAut V := (fL e).comp κ.symm.toMonoidHom
  have hιinj : Function.Injective ι := fun a b hab => κ.symm.injective (fL_injective e hab)
  obtain ⟨E, hE⟩ : ∃ E, E = Y.map ι := ⟨_, rfl⟩
  have hEL : E ≤ L := by
    rw [hE]
    rintro _ ⟨g, -, rfl⟩
    exact fL_mem e _
  have hEe : IsElemAbelian2 E := by
    rw [hE]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hYc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, pow_two, hY2 a ha, map_one]
  have hEcard : Nat.card E = Nat.card Y := by
    rw [hE]
    exact Subgroup.card_map_of_injective hιinj
  have hEne : E ≠ ⊥ := by
    rw [hE, Ne, Subgroup.map_eq_bot_iff_of_injective Y hιinj]
    exact hY1
  have hEA2 : IsA2 G E := ⟨hEL.trans hLG, hEne, hEe⟩
  have hact : ∀ (u : G5) (v : V),
      β (Additive.ofMul (ι u v)) = ρ' u (β (Additive.ofMul v)) := fun u v => by
    have h1 := hβ (κ.symm u) (Additive.ofMul v)
    rw [MulEquiv.apply_symm_apply, repOf_apply, ← fL_apply] at h1
    exact h1
  have hfix : Nat.card (fixV E) = Nat.card {x : W // ∀ u ∈ Y, ρ' u x = x} := by
    refine Nat.card_congr
      { toFun := fun v => ⟨β (Additive.ofMul (v : V)), fun u hu => ?_⟩
        invFun := fun x => ⟨Additive.toMul (β.symm x.1), ?_⟩
        left_inv := fun v => Subtype.ext ?_
        right_inv := fun x => Subtype.ext ?_ }
    · rw [← hact, v.2 (ι u) (hE ▸ ⟨u, hu, rfl⟩)]
    · intro y hy
      rw [hE] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      apply Additive.ofMul.injective
      apply β.injective
      rw [hact, ofMul_toMul, LinearEquiv.apply_symm_apply]
      exact x.2 u hu
    · change Additive.toMul (β.symm (β (Additive.ofMul (v : V)))) = v
      rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
    · change β (Additive.ofMul (Additive.toMul (β.symm x.1))) = x.1
      rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
  have hVW : Nat.card V = Nat.card W :=
    Nat.card_congr ((Additive.ofMul : V ≃ Additive V).trans β.toEquiv)
  have hr : rAV E ≤ 1 := by
    refine (rAV_le_one_iff hV hEA2).2 ?_
    rw [hVW, hEcard, hfix]
    exact hcard
  exact qhatOf_le_one_of_rAV_le_one hV hEA2 hr

theorem R4_ne_bot : R4 ≠ ⊥ := by
  intro h
  have := card_R4
  rw [h, Subgroup.card_bot] at this
  norm_num at this

theorem card_fixN_R4 : 16 ≤ Nat.card {x : Fin 5 → ZMod 2 // ∀ u ∈ R4, natRep u x = x} := by
  classical
  have h16 : (Finset.univ.filter fun x : Fin 5 → ZMod 2 => x 4 = 0).card = 16 := by decide
  rw [← h16, ← Nat.card_eq_finsetCard (Finset.univ.filter _)]
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1, fun u hu => ?_⟩) ?_
  · obtain ⟨w, -, hw⟩ := mem_R4_iff.1 hu
    have hx : x.1 4 = 0 := (Finset.mem_filter.1 x.2).2
    rw [natRep_apply, hw, add_mulVec, one_mulVec, vecMulVec_mulVec_eq]
    simp [dotProduct, Pi.single_apply, hx]
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'

theorem qhatOf_le_one_nat5 (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5)
    (β : Additive V ≃ₗ[ZMod 2] (Fin 5 → ZMod 2))
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = natRep (κ g) (β w)) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  refine qhatOf_le_one_of_sub5 hV hHyp e natRep κ β hβ R4 comm_R4 sq_R4 R4_ne_bot ?_
  rw [card_R4, Nat.card_eq_fintype_card (α := Fin 5 → ZMod 2), Fintype.card_fun, ZMod.card]
  calc 2 ^ Fintype.card (Fin 5) = 16 * 2 := by norm_num
    _ ≤ 16 * Nat.card {x : Fin 5 → ZMod 2 // ∀ u ∈ R4, natRep u x = x} :=
      Nat.mul_le_mul_left _ (card_fixN_R4.trans' (by norm_num))

theorem qhatOf_le_one_wedge5 (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5)
    (β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2))
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w)) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  refine qhatOf_le_one_of_sub5 hV hHyp e wedgeRep κ β hβ R4 comm_R4 sq_R4 R4_ne_bot ?_
  have h64 : 64 ≤ Nat.card {x : Fin 10 → ZMod 2 // ∀ u ∈ R4, wedgeRep u x = x} := by
    refine card_fixW_R4.trans (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)).le
    exact forall₂_congr fun u _ => by rw [wedgeRep_apply']
  rw [card_R4, Nat.card_eq_fintype_card (α := Fin 10 → ZMod 2), Fintype.card_fun, ZMod.card]
  calc 2 ^ Fintype.card (Fin 10) = 16 * 64 := by norm_num
    _ ≤ 16 * Nat.card {x : Fin 10 → ZMod 2 // ∀ u ∈ R4, wedgeRep u x = x} :=
      Nat.mul_le_mul_left _ h64

end FF

theorem type_trichotomy : ∀ J : Fin 4 → Bool, J ∈ typeList ∨ J = J24 ∨
    ∀ s t : Fin 4, s ≠ t → J s = true ∨ J t = true := by
  decide

end B45L5

namespace B45L5

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem qhatOf_le_one_of_twoF
    [Module (ZMod 2) (Additive V)] (hV : ∀ v : V, v ^ 2 = 1)
    (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2)))
    (hA : IsA2 G A) (h2F : (fixV A).index ≤ Nat.card A ^ 2) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  classical
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Nontrivial V := nontrivial_of_equiv e
  have hρ : IsSimpleRep (repOf (phiOf e)) :=
    isSimpleRep_repOf (phiOf e) (irr_of_isIrrSec hHyp.2.2.2)
  have : Nontrivial (Additive V) := hρ.1
  obtain ⟨y, hy, hy0, -⟩ := exists_eigen (repOf (phiOf e))
  obtain ⟨J, hJ⟩ : ∃ J : Fin 4 → Bool, ∀ s, Th (repOf (phiOf e)) s y = 0 ↔ J s = true :=
    ⟨fun s => decide (Th (repOf (phiOf e)) s y = 0), fun s => by rw [decide_eq_true_iff]⟩
  rcases type_trichotomy J with hJm | hJa | hJu
  ·
    refine (false_of_disp hHyp hZ e hA h2F fun x hx2 hx1 => ?_).elim
    obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 hx2 hx1
    · rw [← finrank_range_conj _ hc]
      exact thirteen_le_t hρ hy hy0 hJm hJ
    · rw [← finrank_range_conj _ hc]
      exact thirteen_le_s hρ hy hy0 hJm hJ
  ·
    obtain ⟨β, hβ⟩ := iso_rep24 hρ hy hy0 (hJa ▸ hJ)
    exact (false_of_adj hHyp hZ hβ hA h2F).elim
  ·
    have hu : ∀ s t : Fin 4, s ≠ t →
        Th (repOf (phiOf e)) s y = 0 ∨ Th (repOf (phiOf e)) t y = 0 := fun s t hst =>
      ((hJu s t hst).imp (hJ s).mpr (hJ t).mpr)
    rcases l5Model_of_unique hρ hy hy0 hu with htriv | ⟨κ, β, hβ⟩ | ⟨κ, β, hβ⟩
    · exact (not_trivial e htriv).elim
    · exact qhatOf_le_one_nat5 hV hHyp e κ β hβ
    · exact qhatOf_le_one_wedge5 hV hHyp e κ β hβ

end B45L5

open B45L5 in
theorem asB45L52_holds :
    AsB45L52 := by
  intro V _ _ hV G L hHyp hP hq
  obtain ⟨A, hA, -, hcard⟩ := exists_cubic_of_qhatOf_le_two hV hq
  obtain ⟨hZ, hmodel⟩ := hP
  obtain ⟨e⟩ := exists_statedSL_of_model hZ hmodel
  let : Module (ZMod 2) (Additive V) := zmod2Mod hV
  have h2F : (fixV A).index ≤ Nat.card A ^ 2 := by
    rw [← (fixV A).index_mul_card] at hcard
    exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  exact qhatOf_le_one_of_twoF hV hHyp hZ e hA h2F

end CFSG.Quasithin
