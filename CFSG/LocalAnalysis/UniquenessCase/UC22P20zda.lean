module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_two_ctx (hu38 : uc22p20oU38Witness) (D : Data G) {L K K₂ : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K)
    (hLK : L = K ⊔ K₂) {t : G} (htT : t ∈ D.T) (ht : K₂ = uc22p20bCj t K) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n ∨ (n = 3 ∧ IsSU3 (Bar2 K) 3)) :
    UC22pwtCtx (uc22pwIndHom L D.T hL.1) ⟨t, htT⟩ (uc22p20iSylowBar D L) (uc22pwuImg L K) (uc22pwuImg L K₂) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (uc22p20iSylowBar D L ⊓ uc22pwuImg L K) (uc22pwuImg L K) ∧
      CFSG.Open.IsQuasisimple ↥(uc22pwuImg L K) ∧
      (IsSz ↥(uc22pwuImg L K) n ∨ IsL2 ↥(uc22pwuImg L K) n ∨ IsSU3 ↥(uc22pwuImg L K) n) ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥(uc22pwuImg L K)) := by
  have hKL : K ≤ L := CFSG.Open.IsSubnormal.le hK.1
  have hK₂L : K₂ ≤ L := CFSG.Open.IsSubnormal.le hK₂.1
  obtain ⟨e₁', -⟩ := uc22p20d_bar2Equiv hKL hK.1
  have e₁ : Bar2 K ≃* ↥(uc22pwuImg L K) := e₁'
  have hcomm : ∀ a ∈ uc22pwuImg L K, ∀ b ∈ uc22pwuImg L K₂, a * b = b * a :=
    uc22p20d_commute_images (uc22p20o_oTwoE_top D hL) (uc22p20e_cComp_of_calC hK)
      (uc22p20e_cComp_of_calC hK₂) hne.symm
  have hsup := uc22pwu_sup_img hKL hK₂L hLK
  have htK₂ : uc22p20bCj t K₂ = K := by
    rcases uc22pwu_perm D hL hK hK₂ hne hLK (hL.1 htT) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (ht.trans h1) hne
    · exact h2
  have hτ₁ : ∀ x, x ∈ uc22pwuImg L K ↔ uc22pwIndHom L D.T hL.1 ⟨t, htT⟩ x ∈ uc22pwuImg L K₂ :=
    fun x => uc22pwu_swap hL hKL ⟨t, htT⟩ ht.symm x
  have hτ₂ : ∀ x, x ∈ uc22pwuImg L K₂ ↔ uc22pwIndHom L D.T hL.1 ⟨t, htT⟩ x ∈ uc22pwuImg L K :=
    fun x => uc22pwu_swap hL hK₂L ⟨t, htT⟩ htK₂ x
  have hperm : ∀ g : ↥D.T,
      ((∀ x, x ∈ uc22pwuImg L K ↔ uc22pwIndHom L D.T hL.1 g x ∈ uc22pwuImg L K) ∧
        (∀ x, x ∈ uc22pwuImg L K₂ ↔ uc22pwIndHom L D.T hL.1 g x ∈ uc22pwuImg L K₂)) ∨
      ((∀ x, x ∈ uc22pwuImg L K ↔
          uc22pwIndHom L D.T hL.1 ((⟨t, htT⟩ : ↥D.T)⁻¹ * g) x ∈ uc22pwuImg L K) ∧
        (∀ x, x ∈ uc22pwuImg L K₂ ↔
          uc22pwIndHom L D.T hL.1 ((⟨t, htT⟩ : ↥D.T)⁻¹ * g) x ∈ uc22pwuImg L K₂)) := by
    intro g
    rcases uc22pwu_perm D hL hK hK₂ hne hLK (hL.1 g.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨fun x => uc22pwu_swap hL hKL g h1 x, fun x => uc22pwu_swap hL hK₂L g h2 x⟩
    · refine Or.inr ⟨fun x => uc22pwu_swap hL hKL _ ?_ x, fun x => uc22pwu_swap hL hK₂L _ ?_ x⟩
      · show uc22p20bCj (t⁻¹ * (g : G)) K = K
        rw [← uc22p20b_cj_cj, h1, ht, uc22pwu_cj_inv_cj]
      · show uc22p20bCj (t⁻¹ * (g : G)) K₂ = K₂
        rw [← uc22p20b_cj_cj, h2, ← htK₂, uc22pwu_cj_inv_cj]
  have hUinv : ∀ (g : ↥D.T) (x : Bar2 L), x ∈ uc22p20iSylowBar D L ↔
      uc22pwIndHom L D.T hL.1 g x ∈ uc22p20iSylowBar D L :=
    fun g x => uc22p20u_ind_sylowBar D hL (hL.1 g.2) g.2 x
  obtain ⟨hUsplit, hUsyl⟩ := uc22pwu_sylowBar (K := K) (K₂ := K₂) hL hcomm hsup
  have hq : CFSG.Open.IsQuasisimple ↥(uc22pwuImg L K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e₁.symm hK.2.2
  have hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥(uc22pwuImg L K)) := by
    intro p hp hpd
    rw [uc22pwu_card_center_eq e₁]
    exact uc22pwu_hZ hu38 hK.2.2 (uc22p20p_odd_center_bar2 ↥K) hn hsh p hp hpd
  exact ⟨⟨hcomm, hsup, hτ₁, hτ₂, hperm, hUinv, hUsplit⟩, hUsyl, hq, uc22pwu_shape_equiv e₁ hsh, hZ⟩

theorem uc22pw_good_two (hR1 : uc22pwCartanRankOne) (hu38 : uc22p20oU38Witness) (D : Data G)
    {L K K₂ : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K)
    (hLK : L = K ⊔ K₂) {t : G} (htT : t ∈ D.T) (ht : K₂ = uc22p20bCj t K) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n ∨ (n = 3 ∧ IsSU3 (Bar2 K) 3)) :
    ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E := by
  obtain ⟨C, hUsyl, hq, hsh', hZ⟩ := uc22pw_two_ctx hu38 D hL hK hK₂ hne hLK htT ht hn hsh
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  obtain ⟨E, hEU, hab, hodd, hrank, hpi, hinv, hα, hw⟩ :=
    uc22pwt_core hR1 D.sylowM.isPGroup (uc22pwIndHom L D.T hL.1) ⟨t, htT⟩ C.comm C.sup C.swap₁ C.swap₂ C.perm
      C.Uinv C.Usplit hUsyl hq hn hsh' hZ hm' hnem
  exact ⟨E, uc22pw_good_of_induced D hL hm' hnem hEU hab hodd hrank hpi hinv hα hw⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
