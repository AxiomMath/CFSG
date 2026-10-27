module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4Proof
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGProper
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGD4TrialityAutRankInn {R : Type} [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A → ∀ φ ∈ A,
    (¬ ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) →
    (∀ a ∈ A, (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, a = u * f) → a ∈ I) → Nat.card A ≤ 27

namespace NbrGraphD4

open CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_27_of_inner {A : Subgroup (MulAut (Om8 K))} (hA : IsElemAbelian 3 A)
    {α : MulAut (Om8 K)} (hαA : α ∈ A) (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (hAI : ∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K)) :
    Nat.card A ≤ 27 := by
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) :=
    card_le_three_mul hαA fun a ha => exists_mul_pow_mem_sup (hA.2 a ha) hα3 hα
  have h9 := card_inf_inner_le_nine hA hαA hα
  have h2 : Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) ≤
      Nat.card ↥(A ⊓ Inn (Om8 K)) :=
    Subgroup.card_le_of_le fun a ha => ⟨ha.1, hAI a ha.1 ha.2⟩
  omega

theorem ggD4TrialityAutRankInn_omegaPlus :
    GGD4TrialityAutRankInn (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro A hA φ hφA hnot hAI
  set Θ := RecipeFieldOmega.plusEquiv (K := K) one_le_four
  set c := MulAut.congr Θ
  have hA' : IsElemAbelian 3 (A.map c.toMonoidHom) := TableB.isElemAbelian_map hA _
  have h := card_le_27_of_inner hA' (α := c φ) ⟨φ, hφA, rfl⟩
    (fun h => hnot (exists_inner_mul_field_of_mem h)) (by
      rintro _ ⟨a, ha, rfl⟩ hmem
      exact (RecipeFieldOmega.mem_innSet_iff_congr Θ a).1
        (hAI a ha (exists_inner_mul_field_of_mem hmem)))
  rwa [Subgroup.card_map_of_injective c.injective] at h

end NbrGraphD4

theorem largeEvenLabelAll_d4TrialityAutRankInn {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) : LargeEvenLabelAll lab fun _ _ I F => GGD4TrialityAutRankInn I F := by
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ _ => ?_
  rw [h4]
  exact NbrGraphD4.ggD4TrialityAutRankInn_omegaPlus

namespace NbrGraphD4Small

open CFSG.RankThree.CentralCover

variable {G : Type} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R}

theorem inv_apply_mem_of_forall_mem [Finite R] {φ : MulAut R} {W : Subgroup R}
    (h : ∀ w ∈ W, φ w ∈ W) : ∀ w ∈ W, φ⁻¹ w ∈ W := by
  have hle : W.map φ.toMonoidHom ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have heq : W.map φ.toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective φ.injective).ge
  intro w hw
  rw [← heq] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  change φ⁻¹ (φ w') ∈ W
  rwa [MulAut.inv_apply_self]

theorem mem_normalizer_comap_of_inv [Finite G] {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {W : Subgroup R} (hW : ∀ w ∈ W, (ggLAut K θ ⟨g, hg⟩)⁻¹ w ∈ W) :
    g ∈ Subgroup.normalizer (((W.comap (ggQuotHom θ)).map K.subtype : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun h hh => ?_
  obtain ⟨k, hk, rfl⟩ := hh
  have hgi : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hg
  have hk' : g⁻¹ * (k : G) * g⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgi k).mp k.2
  refine ⟨⟨_, hk'⟩, ?_, by simp⟩
  show ggQuotHom θ ⟨_, hk'⟩ ∈ W
  rw [L45KG.ggQuotHom_conj hgi k.2 hk']
  have e : (⟨g⁻¹, hgi⟩ : Subgroup.normalizer (K : Set G)) = (⟨g, hg⟩)⁻¹ := rfl
  rw [e, map_inv]
  exact hW _ hk

theorem isElemAbelian_of_le {E F : Subgroup G} (hF : IsElemAbelian 3 F) (hEF : E ≤ F) :
    IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hF hEF

theorem exists_lift_closure [Finite G] (hKp : commutator K = ⊤)
    (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center K))) {E : Subgroup R}
    (hE : IsElemAbelian 3 E) {T₀ : Set G} (hT₀N : T₀ ⊆ Subgroup.normalizer (K : Set G))
    (hT₀c : ∀ a ∈ T₀, ∀ b ∈ T₀, Commute a b) (hT₀3 : ∀ a ∈ T₀, a ^ 3 = 1)
    (hT₀E : ∀ (t : G) (ht : t ∈ T₀), ∀ e ∈ E, ggLAut K θ ⟨t, hT₀N ht⟩ e = e)
    {W : Subgroup R} (hWE : ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W)
    (hT₀W : ∀ (t : G) (ht : t ∈ T₀), ∀ w ∈ W, (ggLAut K θ ⟨t, hT₀N ht⟩)⁻¹ w ∈ W) :
    ∃ A : Subgroup G, IsElemAbelian 3 A ∧ ∃ hAN : A ≤ Subgroup.normalizer (K : Set G),
      T₀ ⊆ A ∧
      E.map (MulAut.conj : R →* MulAut R) ≤ ((ggLAut K θ).comp (Subgroup.inclusion hAN)).range ∧
      A ≤ Subgroup.normalizer (((W.comap (ggQuotHom θ)).map K.subtype : Subgroup G) : Set G) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hρS : ∀ (g : G) (hg : g ∈ K) (hgN : g ∈ Subgroup.normalizer (K : Set G)),
      ggLAut K θ ⟨g, hgN⟩ = MulAut.conj (ggQuotHom θ ⟨g, hg⟩) :=
    fun g hg _ => ggLAut_mk_self K θ ⟨g, hg⟩
  set S : Set G := {g | ∃ hg : g ∈ K, g ^ 3 = 1 ∧ ggQuotHom θ ⟨g, hg⟩ ∈ E} with hS
  set T : Set G := S ∪ T₀ with hT
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    rintro a ⟨ha, -, haE⟩ b ⟨hb, hb3, hbE⟩
    refine commute_of_ggLAut_commute (θ := θ) hKp hZ3 hb hb3 (Subgroup.le_normalizer ha) ?_
    have hc : Commute (ggQuotHom θ ⟨a, ha⟩) (ggQuotHom θ ⟨b, hb⟩) :=
      mul_comm_of_isElemAbelian hE haE hbE
    rw [hρS a ha, hρS b hb]
    exact (hc.map MulAut.conj).eq
  have hcommST : ∀ t ∈ T₀, ∀ a ∈ S, Commute t a := by
    rintro t ht a ⟨ha, ha3, haE⟩
    refine commute_of_ggLAut_commute (θ := θ) hKp hZ3 ha ha3 (hT₀N ht) ?_
    rw [hρS a ha, D4Rank.mulAut_mul_conj, hT₀E t ht _ haE]
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, Commute a b := by
    rintro a (ha | ha) b (hb | hb)
    · exact hcommS a ha b hb
    · exact (hcommST b hb a ha).symm
    · exact hcommST a ha b hb
    · exact hT₀c a ha b hb
  have hpowT : ∀ a ∈ T, a ^ 3 = 1 := by
    rintro a (ha | ha)
    · exact ha.2.1
    · exact hT₀3 a ha
  set A : Subgroup G := Subgroup.closure T with hA
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => pow_eq_one_of_mem_closure hcommT hpowT ha⟩
    show (a : G) * b = b * a
    exact (commute_of_mem_closure hcommT a.2 b.2).eq
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [hA, Subgroup.closure_le]
    rintro a (ha | ha)
    · exact Subgroup.le_normalizer ha.1
    · exact hT₀N ha
  refine ⟨A, hAel, hAN, fun t ht => Subgroup.subset_closure (Or.inr ht), ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨k, hk3, hke⟩ := L45RankX.exists_lift_of_coprime (θ := θ) hp3 hZ3 (r := e) (m := 1)
      (by rw [pow_one]; exact hE.2 e he)
    have hk3' : (k : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3
    have hq : ggQuotHom θ ⟨(k : G), k.2⟩ = e := by
      rw [ggQuotHom_apply]
      exact hke
    have hkS : (k : G) ∈ S := ⟨k.2, hk3', by rw [hq]; exact he⟩
    have hkA : (k : G) ∈ A := Subgroup.subset_closure (Or.inl hkS)
    refine ⟨⟨k, hkA⟩, ?_⟩
    show ggLAut K θ ⟨(k : G), hAN hkA⟩ = MulAut.conj e
    rw [hρS _ k.2, hq]
  · rw [hA, Subgroup.closure_le]
    rintro a (⟨haK, -, haE⟩ | ha)
    · refine mem_normalizer_comap_of_inv (Subgroup.le_normalizer haK) fun w hw => ?_
      rw [hρS _ haK, ← map_inv, MulAut.conj_apply]
      exact hWE _ (inv_mem haE) w hw
    · exact mem_normalizer_comap_of_inv (hT₀N ha) (hT₀W a ha)

theorem isTwoLocal_normalizer_comap [Finite G] (hZ2 : IsPGroup 2 (Subgroup.center K))
    {W : Subgroup R} (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer
      (((W.comap (ggQuotHom θ)).map K.subtype : Subgroup G) : Set G)) := by
  refine ⟨_, ?_, ?_, rfl⟩
  · obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
    obtain ⟨k, hk⟩ := ggQuotHom_surjective θ (w : R)
    intro hbot
    have hkW : (k : G) ∈ (W.comap (ggQuotHom θ)).map K.subtype :=
      ⟨k, show ggQuotHom θ k ∈ W by rw [hk]; exact w.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hkW
    have hk1 : k = 1 := Subtype.ext hkW
    rw [hk1, map_one] at hk
    exact hw1 (Subtype.ext hk.symm)
  · refine IsPGroup.map ?_ K.subtype
    refine IsPGroup.comap_of_ker_isPGroup hW2 (ggQuotHom θ) ?_
    rw [ker_ggQuotHom]
    exact hZ2

theorem le_twoLocalRank_of_fix [Finite G] (hKp : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K))
    (hinj : Function.Injective (MulAut.conj : R →* MulAut R))
    {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hxInn : ggLAut K θ ⟨x, hxN⟩ ∉ (MulAut.conj : R →* MulAut R).range)
    {Dc : Subgroup G} (hDcK : Dc ≤ Subgroup.centralizer (K : Set G)) (hDc : IsElemAbelian 3 Dc)
    {j : ℕ} (hDcj : Nat.card Dc = 3 ^ j) (hxD : ∀ d ∈ Dc, x * d = d * x)
    {k : ℕ} {E : Subgroup R} (hE : IsElemAbelian 3 E)
    (hEk : Nat.card E = 3 ^ k) (hEφ : ∀ e ∈ E, ggLAut K θ ⟨x, hxN⟩ e = e) {W : Subgroup R}
    (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥) (hWφ : ∀ w ∈ W, ggLAut K θ ⟨x, hxN⟩ w ∈ W)
    (hWE : ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W) :
    k + 1 + j ≤ LargeEvenTwoLocalRank 3 G := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Finite R := Finite.of_surjective θ θ.surjective
  have : Finite (MulAut R) :=
    Finite.of_injective (fun f : MulAut R => (f : R → R)) fun f g h => MulEquiv.ext (congrFun h)
  have hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hρD : ∀ (d : G) (hd : d ∈ Dc) (hdN : d ∈ Subgroup.normalizer (K : Set G)),
      ggLAut K θ ⟨d, hdN⟩ = 1 :=
    fun d hd hdN => ggLAut_eq_one_of_mem_centralizer K θ (g := ⟨d, hdN⟩) (hDcK hd)
  have hT₀N : ({x} ∪ (Dc : Set G) : Set G) ⊆ Subgroup.normalizer (K : Set G) := by
    rintro t (ht | ht)
    · rw [Set.mem_singleton_iff.mp ht]
      exact hxN
    · exact Subgroup.centralizer_le_normalizer _ (hDcK ht)
  obtain ⟨A, hAel, hAN, hT₀A, hcEr, hAW⟩ := exists_lift_closure (θ := θ) hKp hZ3 hE hT₀N
    (by
      rintro a (ha | ha) b (hb | hb)
      · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
      · rw [Set.mem_singleton_iff.mp ha]
        exact hxD b hb
      · rw [Set.mem_singleton_iff.mp hb]
        exact (hxD a ha).symm
      · exact mul_comm_of_isElemAbelian hDc ha hb)
    (by
      rintro a (ha | ha)
      · rw [Set.mem_singleton_iff.mp ha]
        exact hx3
      · exact hDc.2 a ha)
    (by
      rintro t (ht | ht) e he
      · have htx := Set.mem_singleton_iff.mp ht
        subst htx
        exact hEφ e he
      · rw [hρD t ht, MulAut.one_apply])
    hWE
    (by
      rintro t (ht | ht) w hw
      · have htx := Set.mem_singleton_iff.mp ht
        subst htx
        exact inv_apply_mem_of_forall_mem hWφ w hw
      · rw [hρD t ht, inv_one, MulAut.one_apply]
        exact hw)
  set φ := ggLAut K θ ⟨x, hxN⟩ with hφ
  set β : A →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hAN) with hβ
  have hxA : x ∈ A := hT₀A (Or.inl rfl)
  have hDA : Dc ≤ A := fun d hd => hT₀A (Or.inr hd)
  have hker : 3 ^ j ≤ Nat.card β.ker := by
    have hle : Dc.subgroupOf A ≤ β.ker := by
      intro d hd
      rw [MonoidHom.mem_ker]
      exact hρD d hd (hAN d.2)
    have h1 := Subgroup.card_le_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv, hDcj] at h1
  set cE : Subgroup (MulAut R) := E.map (MulAut.conj : R →* MulAut R) with hcE
  have hφr : φ ∈ β.range := ⟨⟨x, hxA⟩, rfl⟩
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [hφ, ← map_pow, h1, map_one]
  have hφ1 : φ ≠ 1 := fun h => hxInn (h ▸ one_mem _)
  have hφo : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hcEcard : Nat.card cE = 3 ^ k := by
    rw [hcE, Subgroup.card_map_of_injective hinj, hEk]
  have hφcomm : ∀ c ∈ cE, c * φ = φ * c := by
    rintro _ ⟨e, he, rfl⟩
    rw [D4Rank.mulAut_mul_conj, hEφ e he]
  have hnorm : Subgroup.zpowers φ ≤ Subgroup.normalizer (cE : Set (MulAut R)) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun c hc => hφcomm c hc))
  have hdisj : Disjoint cE (Subgroup.zpowers φ) := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hc
    by_contra hne
    have hle : Subgroup.zpowers (MulAut.conj e) ≤ Subgroup.zpowers φ :=
      Subgroup.zpowers_le.mpr hc
    have he3 : (MulAut.conj e) ^ 3 = 1 := by rw [← map_pow, hE.2 e he, map_one]
    have ho : orderOf (MulAut.conj e) = 3 := orderOf_eq_prime he3 hne
    have heq : Subgroup.zpowers (MulAut.conj e) = Subgroup.zpowers φ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ho, hφo])
    have hφm : φ ∈ Subgroup.zpowers (MulAut.conj e) := heq ▸ Subgroup.mem_zpowers φ
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hφm
    exact hxInn ⟨e ^ m, by rw [map_zpow, hm]⟩
  have hsup : Nat.card (cE ⊔ Subgroup.zpowers φ : Subgroup (MulAut R)) = 3 ^ k * 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      hcEcard, Nat.card_zpowers, hφo]
  have hrange : 3 ^ k * 3 ≤ Nat.card β.range := by
    rw [← hsup]
    exact Subgroup.card_le_of_le (sup_le hcEr (Subgroup.zpowers_le.mpr hφr))
  have hcardA : 3 ^ (k + 1 + j) ≤ Nat.card A := by
    calc 3 ^ (k + 1 + j) = 3 ^ j * (3 ^ k * 3) := by ring
      _ ≤ Nat.card β.ker * Nat.card β.range := Nat.mul_le_mul hker hrange
      _ = Nat.card A := Subgroup.card_ker_mul_card_range β
  have hle := TableB.card_le_of_twoLocal hp3 (isTwoLocal_normalizer_comap hZ2 hW2 hW1) hAW hAel
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hcardA.trans hle)

theorem le_twoLocalRank_of_local [Finite G] (hKp : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (θ : K ⧸ Subgroup.center K ≃* R)
    (hinj : Function.Injective (MulAut.conj : R →* MulAut R))
    {Dc : Subgroup G} (hDcK : Dc ≤ Subgroup.centralizer (K : Set G)) (hDc : IsElemAbelian 3 Dc)
    {j : ℕ} (hDcj : Nat.card Dc = 3 ^ j) {k : ℕ} {E : Subgroup R} (hE : IsElemAbelian 3 E)
    (hEk : Nat.card E = 3 ^ k) {W : Subgroup R} (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hWE : ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W) :
    k + j ≤ LargeEvenTwoLocalRank 3 G := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hρD : ∀ (d : G) (hd : d ∈ Dc) (hdN : d ∈ Subgroup.normalizer (K : Set G)),
      ggLAut K θ ⟨d, hdN⟩ = 1 :=
    fun d hd hdN => ggLAut_eq_one_of_mem_centralizer K θ (g := ⟨d, hdN⟩) (hDcK hd)
  have hT₀N : (Dc : Set G) ⊆ Subgroup.normalizer (K : Set G) :=
    fun t ht => Subgroup.centralizer_le_normalizer _ (hDcK ht)
  obtain ⟨A, hAel, hAN, hT₀A, hcEr, hAW⟩ := exists_lift_closure (θ := θ) hKp hZ3 hE hT₀N
    (fun a ha b hb => mul_comm_of_isElemAbelian hDc ha hb) (fun a ha => hDc.2 a ha)
    (fun t ht e _ => by rw [hρD t ht, MulAut.one_apply]) hWE
    (fun t ht w hw => by rw [hρD t ht, inv_one, MulAut.one_apply]; exact hw)
  set β : A →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hAN) with hβ
  have hker : 3 ^ j ≤ Nat.card β.ker := by
    have hle : Dc.subgroupOf A ≤ β.ker := by
      intro d hd
      rw [MonoidHom.mem_ker]
      exact hρD d hd (hAN d.2)
    have h1 := Subgroup.card_le_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀A).toEquiv, hDcj] at h1
  have : Finite R := Finite.of_surjective θ θ.surjective
  have : Finite (MulAut R) :=
    Finite.of_injective (fun f : MulAut R => (f : R → R)) fun f g h => MulEquiv.ext (congrFun h)
  have hrange : 3 ^ k ≤ Nat.card β.range := by
    have h1 := Subgroup.card_le_of_le hcEr
    rwa [Subgroup.card_map_of_injective hinj, hEk] at h1
  have hcardA : 3 ^ (k + j) ≤ Nat.card A := by
    calc 3 ^ (k + j) = 3 ^ j * 3 ^ k := by ring
      _ ≤ Nat.card β.ker * Nat.card β.range := Nat.mul_le_mul hker hrange
      _ = Nat.card A := Subgroup.card_ker_mul_card_range β
  have hle := TableB.card_le_of_twoLocal hp3 (isTwoLocal_normalizer_comap hZ2 hW2 hW1) hAW hAel
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hcardA.trans hle)

end NbrGraphD4Small

end CFSG.StandardType
