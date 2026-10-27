module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4B
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4A

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem blockFacts_of_case6 (hBlk : J4BlockFacts) {T M L I H K : Subgroup G}
    (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    K ⊓ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) = perfectCore (L ⊓ H) ∧
      K ⊓ Subgroup.centralizer (pCoreOf 2 (perfectCore (L ⊓ H)) : Set G) =
        pCoreOf 2 (perfectCore (L ⊓ H)) ∧
      (∀ W : Subgroup G, W ≤ pCoreOf 2 (perfectCore (L ⊓ H)) →
        perfectCore (L ⊓ H) ≤ Subgroup.normalizer (W : Set G) →
          W = ⊥ ∨ W = pCoreOf 2 (perfectCore (L ⊓ H))) ∧
      ∃ x ∈ perfectCore (L ⊓ H), orderOf x = 3 ∧
        pCoreOf 2 (perfectCore (L ⊓ H)) ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) ∧
        Nat.card ↥(Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) = 6 ∧
        IsSporadic .M22 (↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) ⧸
          Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) ∧
        ¬ pCoreOf 2 (perfectCore (L ⊓ H)) ⊓ Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer (perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) := by
  obtain ⟨hK, hS, hcase⟩ := h6
  set LH := perfectCore (L ⊓ H) with hLH
  have hLHM : LH ≤ H ⊓ M := (perfectCore_le (L ⊓ H)).trans
    (le_inf inf_le_right (inf_le_left.trans c.hyp421.L_le))
  have hM0 : conjClosure LH (H ⊓ M) = LH := by
    refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (le_conjClosure LH (H ⊓ M))
    exact (Subgroup.mem_normalizer_iff.mp (c.LH_normal hh) z).mp hz
  have hE : IsExt ↥LH (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y) ∨
      IsExt ↥LH (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · left
      have h' : IsExt ↥(conjClosure LH (H ⊓ M)) (fun N _ => IsE2 11 N)
        (fun Y _ => IsSporadic .M24 Y) := h
      rwa [hM0] at h'
    · right
      have h' : IsExt ↥(conjClosure LH (H ⊓ M)) (fun N _ => IsE2 10 N)
        (fun Y _ => IsPSL 5 2 1 Y) := h
      rwa [hM0] at h'
  exact blockFacts hBlk hK c.LH_le hS hE

theorem exists_mem_inf_mul
    (hOut : J4OutTrivial) (hBlk : J4BlockFacts) {T M L Mm I H K : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {i : G} (hi : i ∈ I) :
    ∃ i' ∈ I ⊓ L, i'⁻¹ * i ∈ centralizerSection I L (pCoreOf 2 L) := by
  have hK := h6.1
  set LH := perfectCore (L ⊓ H) with hLH
  have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
  have hLM : L ≤ M := c.hyp421.L_le
  have hiH : i ∈ H := hIH.2 hi
  have hiM : i ∈ M := c.I_le hi
  obtain ⟨k, hk, hkc⟩ := exists_mem_centralizer hOut hK (normal hy hIH c hK hiH)
  set cc := k⁻¹ * i with hcc
  have hccK : ∀ y ∈ K, y * cc = cc * y := fun y hy' => Subgroup.mem_centralizer_iff.mp hkc y hy'
  have hiN : i ∈ Subgroup.normalizer (LH : Set G) := c.LH_normal ⟨hiH, hiM⟩
  have hccN : cc ∈ Subgroup.normalizer (LH : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy'
      rw [← hccK y (c.LH_le hy'), mul_inv_cancel_right]
      exact hy'
    · intro hy'
      have hz := hccK (cc * y * cc⁻¹) (c.LH_le hy')
      have e : y = cc * y * cc⁻¹ := by
        calc y = cc⁻¹ * (cc * y * cc⁻¹) * cc := by group
          _ = cc⁻¹ * (cc * (cc * y * cc⁻¹)) := by rw [mul_assoc, hz]
          _ = cc * y * cc⁻¹ := by group
      rw [e]
      exact hy'
  have hkN : k ∈ Subgroup.normalizer (LH : Set G) := by
    have : k = i * cc⁻¹ := by rw [hcc]; group
    rw [this]
    exact Subgroup.mul_mem _ hiN (Subgroup.inv_mem _ hccN)
  have hkLH : k ∈ LH := by
    have h1 : K ⊓ Subgroup.normalizer (LH : Set G) = LH := (blockFacts_of_case6 hBlk c h6).1
    rw [← h1]
    exact ⟨hk, hkN⟩
  have hMp : conjClosure L T = L := c.conjClosure_eq
  have hLI : L ≤ I ⊔ pCoreOf 2 L := by
    have := hy.gammaStar.1.1.2.2.1
    rwa [hMp] at this
  have hIn : I ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (c.I_le.trans c.normal).trans (normalizer_le_normalizer_pCoreOf 2 L)
  obtain ⟨i₁, hi₁, o, ho, hko⟩ := (mem_sup_of_le_normalizer hIn).mp (hLI (hLHL hkLH))
  have hoL : o ∈ L := pCoreOf_le 2 L ho
  have hi₁L : i₁ ∈ L := by
    have : i₁ = k * o⁻¹ := by rw [← hko]; group
    rw [this]
    exact L.mul_mem (hLHL hkLH) (L.inv_mem hoL)
  refine ⟨i₁, ⟨hi₁, hi₁L⟩, ?_⟩
  have hm : i₁⁻¹ * i = o * cc := by
    rw [hcc, ← hko]
    group
  have hmI : i₁⁻¹ * i ∈ I := I.mul_mem (I.inv_mem hi₁) hi
  have hmM : i₁⁻¹ * i ∈ M := c.I_le hmI
  refine ⟨hmI, c.normal hmM, normalizer_le_normalizer_pCoreOf 2 L (c.normal hmM), ?_⟩
  intro x hx
  rw [hm]
  have hccM : cc ∈ M := by
    rw [hcc]
    exact M.mul_mem (M.inv_mem (hLM (hLHL hkLH))) hiM
  have hccO : cc ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L (c.normal hccM)
  have hLHn : LH ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hLHL.trans (le_normalizer_pCoreOf 2 L)
  obtain ⟨l, hl, o', ho', hx'⟩ := (mem_sup_of_le_normalizer hLHn).mp (c.L_le hx)
  rw [← hx']
  have hcl : cc * l⁻¹ * cc⁻¹ = l⁻¹ := by
    have hcomm : Commute l cc := hccK l (c.LH_le hl)
    rw [← hcomm.inv_left.eq]
    group
  have hq : o' * o * (cc * o'⁻¹ * cc⁻¹) ∈ pCoreOf 2 L :=
    (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).mul_mem ho' ho)
      ((Subgroup.mem_normalizer_iff.mp hccO _).mp ((pCoreOf 2 L).inv_mem ho'))
  have e : l * o' * (o * cc) * (l * o')⁻¹ * (o * cc)⁻¹ =
      l * (o' * o * (cc * o'⁻¹ * cc⁻¹)) * (cc * l⁻¹ * cc⁻¹) * o⁻¹ := by group
  rw [e, hcl]
  refine (pCoreOf 2 L).mul_mem ?_ ((pCoreOf 2 L).inv_mem ho)
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (hLHL hl)) _).mp hq
  exact this

theorem exists_le
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOut : J4OutTrivial)
    (hBlk : J4BlockFacts) {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I)
    (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    ∃ I₂ : Subgroup G, I₂ ≤ I ∧ I₂ ≤ L ⊔ T ∧ pCoreOf 2 I₂ = pCoreOf 2 I ∧
      Hyp4_2_3 G T M L Mm I₂ ∧ InM I₂ H ∧ Conf4212 G T M L I₂ H K ∧
      C48Case6 H (pCoreOf 2 I₂) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K := by
  set R := pCoreOf 2 I with hR
  set I₂ := (I ⊓ L) ⊔ R with hI₂
  have hMp : conjClosure L T = L := c.conjClosure_eq
  have h41 : Hyp4_1_1 G T M (conjClosure L T) := lemma_4_2_2 h37 h38 h39 hy.toHyp4_2_1
  have hRI : R ≤ I := pCoreOf_le 2 I
  have hI₂I : I₂ ≤ I := sup_le inf_le_left hRI
  have hRT : R ≤ T := hy.R_le.trans inf_le_left
  have hI₂LT : I₂ ≤ L ⊔ T := sup_le (inf_le_right.trans le_sup_left) (hRT.trans le_sup_right)
  have hRI₂ : R ≤ pCoreOf 2 I₂ := le_pCoreOf_of_le_normalizer 2 le_sup_right
    (hI₂I.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hR₂ne : pCoreOf 2 I₂ ≠ ⊥ := fun h =>
    hy.gammaStar.1.1.2.2.2 (le_bot_iff.mp (h ▸ hRI₂))
  have hIeq : I₂ ⊔ centralizerSection I (conjClosure L T) (pCoreOf 2 (conjClosure L T)) = I := by
    rw [hMp]
    refine le_antisymm (sup_le hI₂I (centralizerSection_le_left _ _ _)) fun i hi => ?_
    obtain ⟨i', hi', hc⟩ := exists_mem_inf_mul hOut hBlk hy hIH c h6 hi
    have e : i = i' * (i'⁻¹ * i) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hi'))
      (Subgroup.mem_sup_right hc)
  have hMpI : conjClosure L T ⊓ I ≤ I₂ ⊔ pCoreOf 2 (conjClosure L T) := by
    rw [hMp]
    exact fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨hx.2, hx.1⟩)
  have hS := hy.sigma
  have hIMm : I ≤ Mm := hy.gammaStar.1.1.1
  have hι := lemma_4_1_3_one h41 hS hy.gammaStar.1.1 le_rfl hIMm hI₂I hR₂ne hIeq hMpI
  have hInf : I ⊓ conjClosure L T ≤ I₂ ⊓ conjClosure L T := by
    rw [hMp]
    exact fun x hx => ⟨Subgroup.mem_sup_left hx, hx.2⟩
  have hord : OrdLE (conjClosure L T) I I₂ := ⟨hRI₂, hInf⟩
  have hInH₂ : InH I₂ H := ⟨hI₂I.trans c.inH.1, c.inH.2⟩
  have hR₂eq : pCoreOf 2 I₂ = R := by
    refine le_antisymm ?_ hRI₂
    by_contra hnot
    have hlt : R < pCoreOf 2 I₂ := lt_of_le_of_ne hRI₂ fun h => hnot (h ▸ le_rfl)
    have hU := lemma_4_1_3_two h41 hS hy.gammaStar le_rfl hIMm hI₂I hR₂ne hIeq hMpI hord hlt
    have hHM := hU.2 H ⟨hIH.1, hI₂I.trans hIH.2⟩
    exact c.not_le (hHM ▸ le_rfl)
  have hγ : IsGammaStar M (conjClosure L T) Mm I₂ := by
    refine ⟨⟨hι, H, hInH₂, c.not_le⟩, fun I₁ hΓ hle hlt => ?_⟩
    obtain ⟨hle1, hle2⟩ := hle
    rw [hR₂eq] at hle1 hlt
    exact hy.gammaStar.2 I₁ hΓ ⟨hle1, hInf.trans hle2⟩ hlt
  have hy₂ : Hyp4_2_3 G T M L Mm I₂ :=
    { hy with gammaStar := hγ, R_le := by rw [hR₂eq]; exact hy.R_le }
  have c₂ : Conf4212 G T M L I₂ H K :=
    { c with
      I_le := hI₂I.trans c.I_le
      inH := hInH₂
      R_le := by rw [hR₂eq]; exact c.R_le
      hypC28 := by rw [hR₂eq]; exact c.hypC28
      described := by rw [hR₂eq]; exact c.described
      cases := by rw [hR₂eq]; exact c.cases }
  exact ⟨I₂, hI₂I, hI₂LT, hR₂eq, hy₂, ⟨hIH.1, hI₂I.trans hIH.2⟩, c₂, by rw [hR₂eq]; exact h6⟩

end NoJ4

end CFSG.Quasithin.H13.Ch4
