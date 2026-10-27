module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

namespace P22y

theorem commutator_self_le {A : Type} [Group A] (K : Subgroup A) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.2 fun _ ha _ hb => K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem card_commutator_of_card_six {H : Type} [Group H] [Finite H] (h6 : Nat.card H = 6)
    (hZ : Subgroup.center H = ⊥) : Nat.card ↥(⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 (show 3 ^ 1 ∣ Nat.card H by rw [h6]; norm_num)
  rw [pow_one] at hP
  have hidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, h6] at h
    omega
  haveI hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    have hq : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index_eq_card, hidx]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := isCyclic_of_prime_card hq
    letI : CommGroup (H ⧸ P) := IsCyclic.commGroup
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have hab : (a : H ⧸ P) * b = b * a := mul_comm _ _
    rw [hab]
    group
  have hne : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≠ ⊥ := by
    intro hbot
    have h1 : (⊤ : Subgroup H) ≤ Subgroup.centralizer ((⊤ : Subgroup H) : Set H) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot
    have h2 : Subgroup.center H = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact (Subgroup.mem_centralizer_iff.1 (h1 (Subgroup.mem_top x)) y (Subgroup.mem_top y))
    rw [hZ] at h2
    have h3 : Nat.card H = 1 := by
      rw [← Subgroup.card_top (G := H), ← h2, Subgroup.card_bot]
    omega
  have hdvd : Nat.card ↥(⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) ∣ 3 :=
    hP ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact absurd (Subgroup.card_eq_one.1 h1) hne
  · exact h3

theorem card_commutator_factor {A : Type} [Group A] [Finite A] (K : Subgroup A) (h6 : Nat.card K = 6)
    (hZ : Subgroup.center ↥K = ⊥) : Nat.card ↥⁅K, K⁆ = 3 := by
  have hmap : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
  exact card_commutator_of_card_six h6 hZ

theorem card_iSup_of_iSupIndep {A : Type} [Group A] {ι : Type} [Fintype ι] {T : ι → Subgroup A}
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ T i → y ∈ T j → Commute x y) (hind : iSupIndep T) :
    Nat.card ↥(⨆ i, T i) = ∏ i, Nat.card ↥(T i) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hr : (Subgroup.noncommPiCoprod hcomm).range = ⨆ i, T i := Subgroup.noncommPiCoprod_range
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]

end P22y

open P22y

variable {G : Type} [Group G] [Finite G]

theorem uc22p22ye_three_lt_pRank (D : Data G) (Ch : Choice2011 G) (h51 : S22_5_1 D Ch) (h1110 : R1110W D)
    (hW : InCalW D.M D.T D.U) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb)
    (h6 : 6 ≤ (Finset.univ.filter fun k => Nat.card (Nb k) = 6).card) : 3 < CFSG.Open.pRank 3 D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcl := h51 hH c m Nb hNb
  set S : Finset (Fin m) := Finset.univ.filter fun k => Nat.card (Nb k) = 6 with hS
  have hmemS : ∀ k, k ∈ S ↔ Nat.card (Nb k) = 6 := fun k => by simp [hS]
  set T : ↥S → Subgroup (MBar D.M D.U) := fun k => ⁅Nb k, Nb k⁆ with hT
  have hT3 : ∀ k : ↥S, Nat.card ↥(T k) = 3 := by
    intro k
    obtain ⟨n, hn, -⟩ := hcl k
    exact card_commutator_factor (Nb k) ((hmemS k).1 k.2) (center_eq_bot_of_isL2Ev hn)
  have hTle : ∀ k : ↥S, T k ≤ Nb k := fun k => commutator_self_le (Nb k)
  set X : Subgroup (MBar D.M D.U) := ⨆ k : ↥S, T k with hX
  have hXn : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨τ, hτ⟩ := uc22p22ya_exists_perm D hNb hcl g
    have hmap : X.map (MulAut.conj g).toMonoidHom ≤ X := by
      rw [hX, Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      have hk : τ k ∈ S := by
        rw [hmemS, ← hτ k, Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact (hmemS k).1 k.2
      have : (T k).map (MulAut.conj g).toMonoidHom = T ⟨τ k, hk⟩ := by
        rw [hT]
        simp only
        rw [Subgroup.map_commutator, hτ k]
      rw [this]
      exact le_iSup T ⟨τ k, hk⟩
    exact hmap ⟨x, hx, rfl⟩
  have hcommT : Pairwise fun k l : ↥S => ∀ x y : MBar D.M D.U, x ∈ T k → y ∈ T l → Commute x y := by
    intro k l hkl x y hx hy
    exact hNb.1.2.1 k l (fun h => hkl (Subtype.ext h)) x (hTle k hx) y (hTle l hy)
  have hXel : IsElemAbelian 3 X := by
    rw [hX, Subgroup.iSup_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hb
      by_cases hkl : k = l
      · subst hkl
        haveI := isCyclic_of_prime_card (hT3 k)
        letI : CommGroup ↥(T k) := IsCyclic.commGroup
        exact congrArg Subtype.val (mul_comm (⟨a, hk⟩ : ↥(T k)) ⟨b, hl⟩)
      · exact hcommT hkl a b hk hl
    · intro a ha
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
      have h1 : (⟨a, hk⟩ : ↥(T k)) ^ Nat.card ↥(T k) = 1 := pow_card_eq_one'
      rw [hT3] at h1
      exact congrArg Subtype.val h1
  have hind : iSupIndep T :=
    (iSupIndep.comp (P22y.iSupIndep_of hNb.1) Subtype.val_injective).mono fun k => hTle k
  have hXcard : Nat.card X = 3 ^ S.card := by
    rw [hX, card_iSup_of_iSupIndep hcommT hind]
    simp only [hT3, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hXle : X ≤ ⁅(⊤ : Subgroup (MBar D.M D.U)), ⊤⁆ :=
    iSup_le fun k => Subgroup.commutator_mono le_top le_top
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  haveI hN := cTilde_bot_normal D.M D.U hMU
  set e := mbarEquiv D.M D.U with he
  set X' : Subgroup (F11.MBar11 D.M ⊥ D.U) := X.map e.toMonoidHom with hX'
  have hX'n : X'.Normal := hXn.map _ e.surjective
  have hX'el : IsElemAbelian 3 X' := hXel.map _
  have hX'card : Nat.card X' = 3 ^ S.card := by
    rw [hX', Subgroup.card_map_of_injective e.injective, hXcard]
  have hX'le : X' ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ D.U)), ⊤⁆ := by
    rw [hX']
    refine (Subgroup.map_mono hXle).trans ?_
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥(F11.O2p 3 D.M)))
  have hQ : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup ↥(F11.O2p 3 D.M)).map (F11.O2p 3 D.M).subtype)
      (F11.O2p 3 D.M) := ⟨Q, rfl⟩
  have hS1 : 1 < S.card := by omega
  have hrank := ((h1110 D.U (uc22p22c_hyp11 D hW c.hU) 3 Nat.prime_three (by norm_num) _ hQ).2.2
    S.card hS1 X' hX'n hX'el hX'card hX'le).1.2.2.2
  have hO : F11.Omega1p 3 ((Q : Subgroup ↥(F11.O2p 3 D.M)).map (F11.O2p 3 D.M).subtype ⊓ ⁅D.M, D.M⁆ ⊓
      F11.barPreimage11 D.M ⊥ D.U X') ≤ D.M := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨⟨⟨⟨y, -, rfl⟩, -⟩, -⟩, -⟩ := hx
    exact (Subgroup.map_subtype_le _) y.2
  have hmono := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hO
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
