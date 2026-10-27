module

public import CFSG.Milestones.ASVolI.B610.FamC

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_isElemAbelian_mono {E F : Subgroup G} (hFE : F ≤ E)
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 F :=
  ⟨⟨⟨fun x y => Subtype.ext (B2F.isElemAbelian_comm hE (hFE x.2) (hFE y.2))⟩⟩,
    fun x hx => hE.2 x (hFE hx)⟩

theorem burnsideB610_rk_stdMod {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    rk (H.StdMod (Fin 2) F) = 2 * n := by
  unfold rk
  rw [H.card_stdMod, Fintype.card_fin, hF, ← pow_mul, mul_comm, padicValNat.prime_pow]

theorem burnsideB610_isPGroup_stdMod {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : IsPGroup 2 (H.StdMod (Fin 2) F) := by
  refine IsPGroup.of_card (n := 2 * n) ?_
  rw [H.card_stdMod, Fintype.card_fin, hF, ← pow_mul, mul_comm]

theorem burnsideB610_card_fixV_le {F : Type} [Field F] [Finite F]
    {E : Subgroup (MulAut (H.StdMod (Fin 2) F))} (hEim : E ≤ H.natImage (StatedSL 2 F))
    (hE1 : E ≠ ⊥) : Nat.card ↥(fixV E) ≤ Nat.card F := by
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  obtain ⟨γ, hγ⟩ := hEim heE
  have hM : ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    apply he1'
    rw [← hγ]
    refine H.toAddMap_injective fun v => ?_
    rw [H.toAddMap_natAut, H.toAddMap_one, h, Matrix.one_mulVec]
  have hv : ∀ v : ↥(fixV E), ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (v : H.StdMod (Fin 2) F)) =
        Multiplicative.toAdd (v : H.StdMod (Fin 2) F) := fun v => by
    have h1 : e (v : H.StdMod (Fin 2) F) = v := v.2 e heE
    rw [← hγ] at h1
    exact congrArg Multiplicative.toAdd h1
  let j : ↥(fixV E) → {w : Fin 2 → F //
      ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w} :=
    fun v => ⟨Multiplicative.toAdd (v : H.StdMod (Fin 2) F), hv v⟩
  have hj : Function.Injective j := by
    intro v w hvw
    have h1 := Subtype.ext_iff.mp hvw
    exact Subtype.ext (Multiplicative.toAdd.injective h1)
  exact (Nat.card_le_card_of_injective j hj).trans (B42L2.card_fixed_le _ hM)

theorem burnsideB610_img_le_natImage_of_le {L V : Subgroup G} {F : Type} [Field F]
    (D : NatData L V F) (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup G}
    (hYL : Y ≤ L) : D.img Y ≤ H.natImage (StatedSL 2 F) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨D.α ⟨y, hYL (Subgroup.mem_subgroupOf.mp hy)⟩, ?_⟩
  rw [← D.act_of_mem hLV]

theorem burnsideB610_le_centralizer_of_img_eq_bot {L V : Subgroup G} {F : Type} [Field F]
    (D : NatData L V F)
    (hker : ∀ a : ↥(nLV L V), D.act a = 1 →
      (a : G) ∈ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G))
    {Y : Subgroup G} (hY : Y ≤ nLV L V) (h : D.img Y = ⊥) :
    Y ≤ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  intro y hy
  have h1 : D.act ⟨y, hY hy⟩ ∈ D.img Y := ⟨⟨y, hY hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact hker _ h1

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem img_le_natImage [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) {i : ι}
    (hi : i ∈ S) : (D i).img A ≤ CFSG.Quasithin.H.natImage (StatedSL 2 F) := by
  obtain ⟨-, h1, -, -⟩ := hFam.chain hn hF hred hT hA hAV
  have hE := burnsideB610_img_isElemAbelian2 (D i) hA.2.1
  have hW2 := burnsideB610_isPGroup_stdMod hF
  have h2 := rk_add_rkIdx (fixV ((D i).img A))
  have hoff : Nat.card (CFSG.Quasithin.H.StdMod (Fin 2) F) ≤
      Nat.card ((D i).img A) * Nat.card ↥(fixV ((D i).img A)) := by
    rw [card_eq_two_pow_of_isPGroup hW2, card_eq_two_pow_of_isPGroup hE.isPGroup,
      card_eq_two_pow_of_isPGroup (hW2.to_subgroup _), ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [h1 i hi]; omega)
  have hLV : X i ≤ Subgroup.normalizer (V : Set G) := (hFam.le i hi).trans hred.2.1
  exact B69.le_natImage_of_offender hn hF (burnsideB610_img_le_natNorm (D i) hLV A)
    (fun x hx => hE.2 x hx) (fun x hx y hy => hE.1 x hx y hy) hoff

theorem rk_img_eq [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) {i : ι}
    (hi : i ∈ S) (hAi : ¬ A ≤ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) :
    rk ↥((D i).img A) = n := by
  obtain ⟨-, h1, -, -⟩ := hFam.chain hn hF hred hT hA hAV
  have hEim := hFam.img_le_natImage hn hF hred hT hA hAV hi
  have hE := burnsideB610_img_isElemAbelian2 (D i) hA.2.1
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hAnLV : A ≤ nLV (X i) V := fun x hx =>
    ⟨(le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T).trans (hFam.thomp i hi) hx,
      (hT.1.trans hHV) (hA.1 hx)⟩
  have hE1 : (D i).img A ≠ ⊥ := fun h =>
    hAi (burnsideB610_le_centralizer_of_img_eq_bot (D i) (hFam.ker i hi) hAnLV h)
  have hfix := burnsideB610_card_fixV_le hEim hE1
  have hW2 := burnsideB610_isPGroup_stdMod hF
  have hfr : rk ↥(fixV ((D i).img A)) ≤ n := by
    have := card_eq_two_pow_of_isPGroup (hW2.to_subgroup (fixV ((D i).img A)))
    rw [this, hF] at hfix
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hfix
  have hcard := (B42L2.card_le_of_isPGroup hEim hE.isPGroup hn (nl2w_card_natImage hF)).1
  have hrr : rk ↥((D i).img A) ≤ n := by
    rw [card_eq_two_pow_of_isPGroup hE.isPGroup] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have h2 := rk_add_rkIdx (fixV ((D i).img A))
  rw [burnsideB610_rk_stdMod hF] at h2
  have h3 := h1 i hi
  omega

theorem exists_piece [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) {i : ι} (hi : i ∈ S)
    (hAi : ¬ A ≤ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) :
    ∃ B : Subgroup G, B ≤ A ∧ B ≤ X i ∧
      (∀ j ∈ S, j ≠ i → B ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img B) = 2 ^ n ∧
      rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (B : Set G)) + n := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVi : ⁅V, X i⁆ ≤ V := hFam.commutator_le hHV hi
  have hAV : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hAi (h.trans (Subgroup.centralizer_le hVi))
  obtain ⟨hcard, -, hsum, hW⟩ := hFam.chain hn hF hred hT hA hAV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHV
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTV
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
  have hAnLV : ∀ j ∈ S, A ≤ nLV (X j) V := fun j hj x hx =>
    ⟨hAJ.trans (hFam.thomp j hj) hx, hAN hx⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hA.2.1 ha hb
  have hri := hFam.rk_img_eq hn hF hred hT hA hAV hi hAi
  set C : ι → Subgroup G := fun j => Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)
    with hC
  set B : Subgroup G := A ⊓ ⨅ j ∈ S.erase i, C j with hB
  have hBA : B ≤ A := inf_le_left
  have hBc : ∀ j ∈ S, j ≠ i → B ≤ C j := fun j hj hji x hx =>
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx.2 j) (Finset.mem_erase.mpr ⟨hji, hj⟩)
  have hBi : B ⊓ C i = A ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxB, hxi⟩
      refine ⟨hxB.1, hFam.faith hred (hT.1 (hA.1 hxB.1)) fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        exact hxi
      · exact hBc j hj hji hxB
    · rintro x ⟨hxA, hxV⟩
      have hxC : ∀ j ∈ S, x ∈ C j := fun j hj =>
        Subgroup.centralizer_le (hFam.commutator_le hHV hj) hxV
      refine ⟨⟨hxA, ?_⟩, hxC i hi⟩
      exact Subgroup.mem_iInf.mpr fun j => Subgroup.mem_iInf.mpr fun hj =>
        hxC j (Finset.mem_of_mem_erase hj)
  have hsub : rk ↥A ≤ rk ↥B + ∑ j ∈ S.erase i, (rk ↥A - rk ↥(A ⊓ C j)) :=
    burnsideB610_rk_le_sum hAc C (S.erase i)
  have hautI : rk ↥(autI hV A) + rk ↥(A ⊓ Subgroup.centralizer (V : Set G)) = rk ↥A :=
    (burnsideB610_rk_of_card_eq_mul (card_autI_mul_card_inf hV hAN).symm).symm
  have himg : ∀ j ∈ S, rk ↥((D j).img A) + rk ↥(A ⊓ C j) = rk ↥A :=
    fun j hj => burnsideB610_rk_img (D j) (hFam.ker j hj) (hAnLV j hj)
  have hsum_eq : ∑ j ∈ S.erase i, (rk ↥A - rk ↥(A ⊓ C j)) =
      ∑ j ∈ S.erase i, rk ↥((D j).img A) :=
    Finset.sum_congr rfl fun j hj => by
      have := himg j (Finset.mem_of_mem_erase hj)
      omega
  have hsplit : rk ↥((D i).img A) + ∑ j ∈ S.erase i, rk ↥((D j).img A) =
      ∑ j ∈ S, rk ↥((D j).img A) := Finset.add_sum_erase S (fun j => rk ↥((D j).img A)) hi
  have hrkB : n + rk ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤ rk ↥B := by
    rw [hsum_eq] at hsub
    omega
  have hBnLV : B ≤ nLV (X i) V := hBA.trans (hAnLV i hi)
  have himgB := burnsideB610_rk_img (D i) (hFam.ker i hi) hBnLV
  rw [hBi] at himgB
  have hEim : (D i).img B ≤ CFSG.Quasithin.H.natImage (StatedSL 2 F) :=
    (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBA (Subgroup.mem_subgroupOf.mp hx)))).trans
      (hFam.img_le_natImage hn hF hred hT hA hAV hi)
  have hEB := burnsideB610_img_isElemAbelian2 (D i) (burnsideB610_isElemAbelian_mono hBA hA.2.1)
  have hcardB := (B42L2.card_le_of_isPGroup hEim hEB.isPGroup hn (nl2w_card_natImage hF)).1
  have hrkimgB : rk ↥((D i).img B) = n := by
    have hle : rk ↥((D i).img B) ≤ n := by
      rw [card_eq_two_pow_of_isPGroup hEB.isPGroup] at hcardB
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcardB
    omega
  have hcardB' : Nat.card ((D i).img B) = 2 ^ n := by
    rw [card_eq_two_pow_of_isPGroup hEB.isPGroup, hrkimgB]
  have hXiV : X i ≤ Subgroup.normalizer (V : Set G) := (hFam.le i hi).trans hHV
  have hBX : B ≤ X i := by
    intro b hb
    obtain ⟨γ, hγ⟩ := hEim ⟨⟨b, hBnLV hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    obtain ⟨l, rfl⟩ := (D i).surj γ
    have hl := (D i).act_of_mem hXiV l
    set l' : ↥(nLV (X i) V) := ⟨l, Subgroup.le_normalizer l.2, hXiV l.2⟩ with hl'
    have h1 : (D i).act (⟨b, hBnLV hb⟩ * l'⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hγ, hl, mul_inv_cancel]
    have hbl : b * (l : G)⁻¹ ∈ C i := hFam.ker i hi _ h1
    have hbH : b ∈ H := hT.1 (hA.1 (hBA hb))
    have hlH : (l : G) ∈ H := hFam.le i hi l.2
    have hblV : b * (l : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      refine hFam.faith hred (H.mul_mem hbH (H.inv_mem hlH)) fun j hj => ?_
      by_cases hji : j = i
      · subst hji
        exact hbl
      · exact (C j).mul_mem (hBc j hj hji hb)
          ((C j).inv_mem (hFam.triv j hj i hi hji l.2))
    have h2 := hFam.cent i hi ⟨H.mul_mem hbH (H.inv_mem hlH), hblV⟩
    have : b = (b * (l : G)⁻¹) * l := by group
    rw [this]
    exact (X i).mul_mem h2 l.2
  refine ⟨B, hBA, hBX, hBc, hcardB', ?_⟩
  set D' : Subgroup G := A ⊓ C i with hD'
  have hW2 : burnsideB610_famW S X V ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) = V := by
    have hfixA := B2F.rkIdx_fixV_autI hV hAN
    have hWV := hFam.famW_le hHV
    have hcV : ∀ a ∈ burnsideB610_famW S X V, ∀ b ∈ V ⊓ Subgroup.centralizer (A : Set G),
        a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV (hWV ha) hb.1
    have hw1 := B2F.rk_sup_add_rk_inf_of_commute hcV
    have hw2 : burnsideB610_famW S X V ⊓ (V ⊓ Subgroup.centralizer (A : Set G)) =
        burnsideB610_famW S X V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [← inf_assoc, inf_eq_left.mpr hWV]
    rw [hw2] at hw1
    exact B2F.eq_of_le_of_rk_le_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
      (sup_le hWV inf_le_left) (by omega)
  have hCB : V ⊓ Subgroup.centralizer (A : Set G) ≤ V ⊓ Subgroup.centralizer (B : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hBA)
  have hCD : V ⊓ Subgroup.centralizer (A : Set G) ≤ V ⊓ Subgroup.centralizer (D' : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)
  have hWle : burnsideB610_famW S X V ≤ (V ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (D' : Set G)) := by
    refine iSup₂_le fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      refine le_sup_of_le_right (le_inf (hFam.commutator_le hHV hj) ?_)
      exact Subgroup.le_centralizer_iff.mp inf_le_right
    · refine le_sup_of_le_left (le_inf (hFam.commutator_le hHV hj) ?_)
      exact Subgroup.le_centralizer_iff.mp (hBc j hj hji)
  have hVeq : V ≤ (V ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (D' : Set G)) := by
    exact hW2.symm.le.trans (sup_le hWle (hCB.trans le_sup_left))
  have hcBD : ∀ a ∈ V ⊓ Subgroup.centralizer (B : Set G),
      ∀ b ∈ V ⊓ Subgroup.centralizer (D' : Set G), a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV ha.1 hb.1
  have hv1 := B2F.rk_sup_add_rk_inf_of_commute hcBD
  have hv2 : rk ↥((V ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (D' : Set G))) = rk ↥V :=
    le_antisymm (rk_mono (sup_le inf_le_left inf_le_left)) (rk_mono hVeq)
  have hv3 : rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
      rk ↥((V ⊓ Subgroup.centralizer (B : Set G)) ⊓ (V ⊓ Subgroup.centralizer (D' : Set G))) :=
    rk_mono (le_inf hCB hCD)
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hoff := offenderImages_isFFStarOffender hV hVT hTV ⟨A, ⟨hA, hAV⟩, rfl⟩
  have hDN : D' ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hAN
  have hoffD := hoff.2.2.2 (autI hV D') (autI_mono hV inf_le_left)
  rw [card_fixV_autI hV hDN, card_fixV_autI hV hAN] at hoffD
  have hD2 : IsPGroup 2 (autI hV D') :=
    hoff.2.2.1.isPGroup.to_le (autI_mono hV inf_le_left)
  have hV2 : IsPGroup 2 ↥V := B2F.isPGroup_of_isElemAbelian hV
  have hoffD' : rk ↥(autI hV D') + rk ↥(V ⊓ Subgroup.centralizer (D' : Set G)) ≤
      rk ↥(autI hV A) + rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [card_eq_two_pow_of_isPGroup hD2, card_eq_two_pow_of_isPGroup (hV2.to_le inf_le_left),
      card_eq_two_pow_of_isPGroup hoff.2.2.1.isPGroup,
      card_eq_two_pow_of_isPGroup (hV2.to_le inf_le_left), ← pow_add, ← pow_add] at hoffD
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hoffD
  have hautD : rk ↥(autI hV D') + rk ↥(D' ⊓ Subgroup.centralizer (V : Set G)) = rk ↥D' :=
    (burnsideB610_rk_of_card_eq_mul (card_autI_mul_card_inf hV hDN).symm).symm
  have hDV : D' ⊓ Subgroup.centralizer (V : Set G) = A ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hD', inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le (hFam.commutator_le hHV hi))]
  rw [hDV] at hautD
  have hDi : rk ↥((D i).img A) + rk ↥D' = rk ↥A := himg i hi
  have hfixA := B2F.rkIdx_fixV_autI hV hAN
  omega

end burnsideB610_Fam

end CFSG.Quasithin.B610T
