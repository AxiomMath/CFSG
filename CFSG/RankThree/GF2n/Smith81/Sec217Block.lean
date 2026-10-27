module

public import CFSG.RankThree.GF2n.Smith81.Sec217
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

section Component

theorem conjClassSet_eq_of_isConj {z w : G} (h : IsConj z w) : conjClassSet w = conjClassSet z := by
  ext g
  exact ⟨fun hg => h.trans hg, fun hg => h.symm.trans hg⟩

theorem mem_conjClassSet_of_mem_commComponent {z y : G} (h : y ∈ commComponent z) :
    y ∈ conjClassSet z := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, -, hb⟩
  · exact IsConj.refl _
  · exact hb.2.1

theorem commComponent_eq_of_mem {z w : G} (h : w ∈ commComponent z) :
    commComponent w = commComponent z := by
  have hcls : conjClassSet w = conjClassSet z :=
    conjClassSet_eq_of_isConj (mem_conjClassSet_of_mem_commComponent h)
  ext y
  show Relation.ReflTransGen (CommOn (conjClassSet w)) w y ↔
    Relation.ReflTransGen (CommOn (conjClassSet z)) z y
  rw [hcls]
  exact ⟨fun hy => (show Relation.ReflTransGen (CommOn (conjClassSet z)) z w from h).trans hy,
    fun hy => (reflTransGen_commOn_symm
      (show Relation.ReflTransGen (CommOn (conjClassSet z)) z w from h)).trans hy⟩

theorem mem_commComponent_conj_iff (z y g : G) :
    g * y * g⁻¹ ∈ commComponent (g * z * g⁻¹) ↔ y ∈ commComponent z := by
  have hcls : conjClassSet (g * z * g⁻¹) = conjClassSet z :=
    conjClassSet_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩ : IsConj z (g * z * g⁻¹))
  show Relation.ReflTransGen (CommOn (conjClassSet (g * z * g⁻¹))) (g * z * g⁻¹) (g * y * g⁻¹) ↔
    Relation.ReflTransGen (CommOn (conjClassSet z)) z y
  rw [hcls]
  constructor
  · intro h
    have h1 := reflTransGen_commOn_conj (z := z) g⁻¹ h
    have e1 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    have e2 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e1, e2] at h1
  · intro h
    exact reflTransGen_commOn_conj (z := z) g h

theorem mem_normalizer_commComponent_of_conj_mem {z m : G}
    (h : m * z * m⁻¹ ∈ commComponent z) : m ∈ Subgroup.normalizer (commComponent z) := by
  have hc := commComponent_eq_of_mem h
  show ∀ n, n ∈ commComponent z ↔ m * n * m⁻¹ ∈ commComponent z
  intro n
  have h1 := mem_commComponent_conj_iff z n m
  rw [hc] at h1
  exact h1.symm

end Component

section Sylow

theorem mem_commComponent_of_normalizer [Finite G] {z y z₀ : G} {S : Sylow 2 G}
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (commComponent z))
    (hz₀ : z₀ ∈ commComponent z) (hz₀S : ∀ s ∈ (S : Subgroup G), s * z₀ = z₀ * s)
    (hy : y ∈ conjClassSet z) (hyN : y ∈ Subgroup.normalizer (commComponent z))
    (hy2 : y * y = 1) : y ∈ commComponent z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : IsPGroup 2 (Subgroup.zpowers y) := by
    have h1 : orderOf y ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hWN : Subgroup.zpowers y ≤ Subgroup.normalizer (commComponent z) := by
    rw [Subgroup.zpowers_le]
    exact hyN
  obtain ⟨c, hcN, hcW⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.normalizer (commComponent z)) S hSN (Subgroup.zpowers y) hWN hW
  have hcy : c * y * c⁻¹ ∈ (S : Subgroup G) :=
    hcW ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hcomm : c⁻¹ * z₀ * c * y = y * (c⁻¹ * z₀ * c) := by
    have h1 := hz₀S _ hcy
    calc c⁻¹ * z₀ * c * y = c⁻¹ * (z₀ * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * z₀) * c := by rw [← h1]
      _ = y * (c⁻¹ * z₀ * c) := by group
  have hx : c⁻¹ * z₀ * c ∈ commComponent z := by
    have hcN' := Subgroup.inv_mem _ hcN
    have := (show ∀ n, n ∈ commComponent z ↔ c⁻¹ * n * c⁻¹⁻¹ ∈ commComponent z from hcN') z₀
    simpa using this.mp hz₀
  exact Relation.ReflTransGen.tail hx
    ⟨mem_conjClassSet_of_mem_commComponent hx, hy, (hcomm : Commute _ _)⟩

end Sylow

section Configuration

variable [Finite G] {M Q Z : Subgroup G}

theorem exists_sylow_le_M_of_strothHyp (H : StrothHyp M Q Z) :
    ∃ (S : Sylow 2 G) (z₀ : G), z₀ ∈ Z ∧ z₀ ≠ 1 ∧ (S : Subgroup G) ≤ M ∧
      ∀ s ∈ (S : Subgroup G), s * z₀ = z₀ * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hQS⟩ := (isPGroup_Q' H).exists_le_sylow
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hZne : Z ≠ ⊥ := by
    intro h
    have := H.q4
    rw [h, Subgroup.card_bot] at this
    omega
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hQS
    rw [hQS, le_bot_iff] at hZQ
    exact hZne hZQ
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_isPGroup S.isPGroup' hSne)
  have hz₀S : ∀ s ∈ (S : Subgroup G), s * z₀ = z₀ * s := fun s hs =>
    Subgroup.mem_centralizer_iff.mp hz₀.2 s hs
  have hz₀Z : z₀ ∈ Z := by
    have : z₀ ∈ Subgroup.centralizer (Q : Set G) := Subgroup.centralizer_le hQS hz₀.2
    rwa [H.centralizer_Q] at this
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  exact ⟨S, z₀, hz₀Z, hz₀1', fun s hs => mem_M_of_commute_Z H hz₀Z hz₀1' (hz₀S s hs), hz₀S⟩

theorem le_normalizer_commComponent (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    M ≤ Subgroup.normalizer (commComponent z) := by
  intro m hm
  have hw : m * z * m⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) z).mp hz
  have hw1 : m * z * m⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, h]
    group
  obtain ⟨g, -, hg⟩ := Z_isConj H hz hz1 hw hw1
  have hconj : IsConj z (m * z * m⁻¹) := isConj_iff.mpr ⟨g, hg⟩
  exact mem_normalizer_commComponent_of_conj_mem
    (Relation.ReflTransGen.single
      ⟨IsConj.refl z, hconj, H.toHyp79.V_central hz (H.Z_normal.1 hw)⟩)

theorem mem_normalizer_commComponent_of_conj_mem_normalizer (H : StrothHyp M Q Z) {z g : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hg : g⁻¹ * z * g ∈ Subgroup.normalizer (commComponent z)) :
    g ∈ Subgroup.normalizer (commComponent z) := by
  obtain ⟨S, z₀, hz₀Z, hz₀1, hSM, hz₀S⟩ := exists_sylow_le_M_of_strothHyp H
  have hMN := le_normalizer_commComponent H hz hz1
  obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hz₀Z hz₀1
  have hz₀conj : IsConj z z₀ := isConj_iff.mpr ⟨m, hm⟩
  have hz₀comm : z₀ ∈ commComponent z :=
    Relation.ReflTransGen.single
      ⟨IsConj.refl z, hz₀conj, H.toHyp79.V_central hz (H.Z_normal.1 hz₀Z)⟩
  have hyD : g⁻¹ * z * g ∈ conjClassSet z := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hy2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    have h2 : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [h2]; group
  have hyM : g⁻¹ * z * g ∈ commComponent z :=
    mem_commComponent_of_normalizer (S := S) (hSM.trans hMN) hz₀comm hz₀S hyD hg hy2
  have hginv : g⁻¹ ∈ Subgroup.normalizer (commComponent z) :=
    mem_normalizer_commComponent_of_conj_mem (by simpa using hyM)
  simpa using Subgroup.inv_mem _ hginv

end Configuration

theorem smith217UniqueBlock : Smith217UniqueBlockStatement := by
  intro G _ _ M Q Z B _ hc z hz hz1 _ g hg
  exact mem_normalizer_commComponent_of_conj_mem_normalizer hc.ctx.hyp hz hz1 hg

end CFSG.RankThree.GF2n.Smith81
