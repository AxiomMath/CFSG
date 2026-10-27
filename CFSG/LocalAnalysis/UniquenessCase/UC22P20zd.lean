module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22pwuImg (L K : Subgroup G) : Subgroup (Bar2 L) :=
  (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

theorem uc22pwu_map_img {L K : Subgroup G} (hKL : K ≤ L) {g : G} (hg : g ∈ normalizer (L : Set G)) :
    (uc22pwuImg L K).map (uc22p20uInd L g hg).toMonoidHom = uc22pwuImg L (uc22p20bCj g K) := by
  ext y
  constructor
  · rintro ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨⟨g * (l : G) * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg l).1 l.2⟩, ?_,
      (uc22p20uInd_mk L hg l).symm⟩
    exact Subgroup.mem_subgroupOf.2 (uc22p20b_mem_cj.2 ⟨l, Subgroup.mem_subgroupOf.1 hl, rfl⟩)
  · rintro ⟨l', hl', rfl⟩
    obtain ⟨k, hk, hkl⟩ := uc22p20b_mem_cj.1 (Subgroup.mem_subgroupOf.1 hl')
    refine ⟨QuotientGroup.mk ⟨k, hKL hk⟩, ⟨⟨k, hKL hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩, ?_⟩
    show uc22p20uInd L g hg (QuotientGroup.mk ⟨k, hKL hk⟩) = QuotientGroup.mk' _ l'
    rw [uc22p20uInd_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hkl)

theorem uc22pwu_mem_img_iff {L K : Subgroup G} (hKL : K ≤ L) {g : G}
    (hg : g ∈ normalizer (L : Set G)) (x : Bar2 L) :
    x ∈ uc22pwuImg L K ↔ uc22p20uInd L g hg x ∈ uc22pwuImg L (uc22p20bCj g K) := by
  rw [← uc22pwu_map_img hKL hg, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem uc22pwu_swap {D : Data G} {L K K' : Subgroup G} (hL : L ∈ calL D.T D.M) (hKL : K ≤ L)
    (g : ↥D.T) (hg : uc22p20bCj (g : G) K = K') (x : Bar2 L) :
    x ∈ uc22pwuImg L K ↔ uc22pwIndHom L D.T hL.1 g x ∈ uc22pwuImg L K' := by
  rw [← hg]
  exact uc22pwu_mem_img_iff hKL (hL.1 g.2) x

theorem uc22pwu_cj_inv_cj (s : G) (K : Subgroup G) : uc22p20bCj s⁻¹ (uc22p20bCj s K) = K := by
  rw [uc22p20b_cj_cj, inv_mul_cancel, uc22p20b_cj_one]

theorem uc22pwu_cj_injective (s : G) {A B : Subgroup G} (h : uc22p20bCj s A = uc22p20bCj s B) : A = B := by
  have := congrArg (uc22p20bCj s⁻¹) h
  rwa [uc22pwu_cj_inv_cj, uc22pwu_cj_inv_cj] at this

theorem uc22pwu_sup_img {L K K₂ : Subgroup G} (hKL : K ≤ L) (hK₂L : K₂ ≤ L) (hLK : L = K ⊔ K₂) :
    uc22pwuImg L K ⊔ uc22pwuImg L K₂ = ⊤ := by
  have hsup : K.subgroupOf L ⊔ K₂.subgroupOf L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hK₂L, ← hLK, Subgroup.map_top, Subgroup.range_subtype]
  unfold uc22pwuImg
  rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem uc22pwu_cComp_cases (D : Data G) {L K K₂ : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K) (hLK : L = K ⊔ K₂) {C : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp L) : C = K ∨ C = K₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCK, hCK₂⟩ := hcon
  have hOT := uc22p20o_oTwoE_top D hL
  have hKc := uc22p20e_cComp_of_calC hK
  have hK₂c := uc22p20e_cComp_of_calC hK₂
  have hKL : K ≤ L := CFSG.Quasithin.le_of_mem_cComp hKc
  have hK₂L : K₂ ≤ L := CFSG.Quasithin.le_of_mem_cComp hK₂c
  have hCL : C ≤ L := CFSG.Quasithin.le_of_mem_cComp hC
  have h1 := uc22p20d_commute_images hOT hC hKc hCK
  have h2 := uc22p20d_commute_images hOT hC hK₂c hCK₂
  have hsup := uc22pwu_sup_img hKL hK₂L hLK
  have hcen : ∀ a ∈ uc22pwuImg L C, ∀ b : Bar2 L, a * b = b * a := by
    intro a ha b
    have hle : uc22pwuImg L K ⊔ uc22pwuImg L K₂ ≤ Subgroup.centralizer {a} := by
      refine sup_le (fun b hb => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]; exact h1 a ha b hb
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]; exact h2 a ha b hb
    have hb : b ∈ Subgroup.centralizer {a} := hle (hsup ▸ Subgroup.mem_top b)
    exact Subgroup.mem_centralizer_iff.1 hb a (Set.mem_singleton a)
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hCL (CFSG.Quasithin.subnormal_of_mem_cComp hC)
  obtain ⟨x, y, hxy⟩ := uc22p20g_nonab_of_quasisimple (uc22p20p_mem_calC D hL hC).2.2
  refine hxy (e.injective (Subtype.ext ?_))
  rw [map_mul, map_mul]
  exact hcen _ (e x).2 _

theorem uc22pwu_cj_mem_cComp {L C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp L) {s : G}
    (hs : s ∈ normalizer (L : Set G)) : uc22p20bCj s C ∈ CFSG.Quasithin.cComp L := by
  have h := CFSG.Quasithin.cComp_map_mulEquiv (MulAut.conj s) hC
  have hH : L.map (MulAut.conj s).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hs
  rw [hH] at h
  exact h

theorem uc22pwu_perm (D : Data G) {L K K₂ : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K) (hLK : L = K ⊔ K₂) {s : G}
    (hs : s ∈ normalizer (L : Set G)) :
    (uc22p20bCj s K = K ∧ uc22p20bCj s K₂ = K₂) ∨ (uc22p20bCj s K = K₂ ∧ uc22p20bCj s K₂ = K) := by
  have h1 := uc22pwu_cComp_cases D hL hK hK₂ hne hLK
    (uc22pwu_cj_mem_cComp (uc22p20e_cComp_of_calC hK) hs)
  have h2 := uc22pwu_cComp_cases D hL hK hK₂ hne hLK
    (uc22pwu_cj_mem_cComp (uc22p20e_cComp_of_calC hK₂) hs)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (uc22pwu_cj_injective s (h1.trans h2.symm)).symm hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (uc22pwu_cj_injective s (h1.trans h2.symm)).symm hne

theorem uc22pwu_sylowBar {D : Data G} {L K K₂ : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hcomm : ∀ a ∈ uc22pwuImg L K, ∀ b ∈ uc22pwuImg L K₂, a * b = b * a)
    (hsup : uc22pwuImg L K ⊔ uc22pwuImg L K₂ = ⊤) :
    uc22p20iSylowBar D L ≤
        (uc22p20iSylowBar D L ⊓ uc22pwuImg L K) ⊔ (uc22p20iSylowBar D L ⊓ uc22pwuImg L K₂) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (uc22p20iSylowBar D L ⊓ uc22pwuImg L K) (uc22pwuImg L K) :=
  ⟨(uc22p20p_sylow_split hcomm hsup (uc22p20p_sylowBar_isSylowOf D hL)).le,
    uc22p20p_isSylowOf_inf_left hcomm hsup (uc22p20p_sylowBar_isSylowOf D hL)⟩

theorem uc22pwu_shape_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (hsh : IsSz X n ∨ IsL2 X n ∨ (n = 3 ∧ IsSU3 X 3)) : IsSz Y n ∨ IsL2 Y n ∨ IsSU3 Y n := by
  rcases hsh with h | h | ⟨rfl, h⟩
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (uc22p20p_isSU3_of_mulEquiv e h))

theorem uc22pwu_card_center_eq {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center X) := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.card_map_of_injective e.injective

theorem uc22pwu_hZ (hu38 : uc22p20oU38Witness) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X))) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz X n ∨ IsL2 X n ∨ (n = 3 ∧ IsSU3 X 3)) :
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center X) := by
  intro p hp hpd hpZ
  rcases hsh with hsh | hsh | ⟨rfl, hsu⟩
  · rw [uc22p20g_center_bot_of_simple hq (uc22p20g_simple_nonab_SzL2 hn (Or.inl hsh)).1,
      Subgroup.card_bot] at hpZ
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpZ)
  · rw [uc22p20g_center_bot_of_simple hq (uc22p20g_simple_nonab_SzL2 hn (Or.inr hsh)).1,
      Subgroup.card_bot] at hpZ
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpZ)
  · obtain ⟨-, hU⟩ := hsu
    have h3 := (hu38 X hq hodd hU).1
    have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hpd)
    subst hp7
    exact absurd (Nat.le_of_dvd (by norm_num) (hpZ.trans h3)) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22
