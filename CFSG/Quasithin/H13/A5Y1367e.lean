module

public import CFSG.Quasithin.H13.A5Y1367d
public import CFSG.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section List

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commutator_le_of_zpowers {M J : Subgroup (MulAut V)} {t : MulAut V}
    (hJ : J = M ⊔ Subgroup.zpowers t) (ht : t ∈ Subgroup.normalizer (M : Set (MulAut V))) :
    ⁅J, J⁆ ≤ M := by
  have htk : ∀ k : ℤ, t ^ k ∈ Subgroup.normalizer (M : Set (MulAut V)) :=
    fun k => Subgroup.zpow_mem _ ht k
  have hconj : ∀ (k : ℤ) {m : MulAut V}, m ∈ M → t ^ k * m * (t ^ k)⁻¹ ∈ M :=
    fun k m hm => (Subgroup.mem_normalizer_iff.mp (htk k) m).mp hm
  let S : Subgroup (MulAut V) :=
    { carrier := {g | ∃ m ∈ M, ∃ k : ℤ, g = m * t ^ k}
      one_mem' := ⟨1, M.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨m₁, hm₁, a, rfl⟩ ⟨m₂, hm₂, b, rfl⟩
        refine ⟨m₁ * (t ^ a * m₂ * (t ^ a)⁻¹), M.mul_mem hm₁ (hconj a hm₂), a + b, ?_⟩
        rw [zpow_add]
        group
      inv_mem' := by
        rintro _ ⟨m, hm, k, rfl⟩
        refine ⟨t ^ (-k) * m⁻¹ * (t ^ (-k))⁻¹, hconj (-k) (M.inv_mem hm), -k, ?_⟩
        group }
  have hJS : J ≤ S := by
    rw [hJ]
    refine sup_le (fun m hm => ⟨m, hm, 0, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, M.one_mem, 1, by simp⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨m₁, hm₁, a, rfl⟩ := hJS hx
  obtain ⟨m₂, hm₂, b, rfl⟩ := hJS hy
  have e : ⁅m₁ * t ^ a, m₂ * t ^ b⁆ =
      m₁ * (t ^ a * m₂ * (t ^ a)⁻¹) * (t ^ b * m₁⁻¹ * (t ^ b)⁻¹) * m₂⁻¹ := by
    have hab : t ^ b * (t ^ a)⁻¹ = (t ^ a)⁻¹ * t ^ b := by
      rw [← zpow_neg, ← zpow_add, ← zpow_add, add_comm]
    rw [commutatorElement_def]
    calc m₁ * t ^ a * (m₂ * t ^ b) * (m₁ * t ^ a)⁻¹ * (m₂ * t ^ b)⁻¹
        = m₁ * t ^ a * m₂ * (t ^ b * (t ^ a)⁻¹) * m₁⁻¹ * (t ^ b)⁻¹ * m₂⁻¹ := by group
      _ = m₁ * t ^ a * m₂ * ((t ^ a)⁻¹ * t ^ b) * m₁⁻¹ * (t ^ b)⁻¹ * m₂⁻¹ := by rw [hab]
      _ = m₁ * (t ^ a * m₂ * (t ^ a)⁻¹) * (t ^ b * m₁⁻¹ * (t ^ b)⁻¹) * m₂⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ (hconj a hm₂)) (hconj b (M.inv_mem hm₁)))
    (M.inv_mem hm₂)

omit [Finite V] in
theorem mem_normalizer_sup {G₁ G₂ : Subgroup (MulAut V)} {t : MulAut V}
    (ht₁ : t ∈ Subgroup.normalizer (G₁ : Set (MulAut V)))
    (ht₂ : t ∈ Subgroup.normalizer (G₂ : Set (MulAut V))) :
    t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht₁, Subgroup.mem_normalizer_iff_map_conj_eq.mp ht₂]

theorem b56List_of_qs_normal {J N : Subgroup (MulAut V)} (hNJ : N ≤ J)
    (hNn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N)
    (h : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56QuasisimpleList ↥N := by
  rcases h with h1 | h2 | h3 | h4 | h5
  ·
    obtain ⟨hqF, -, hlist⟩ := h1
    have hFJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
    have hFsub : IsSubnormal (quasithinGenFitting J) J :=
      IsSubnormal.step hFJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hFJ).2
        (le_normalizer_quasithinGenFitting J)) (IsSubnormal.refl J)
    rcases B113.component_le_or_commutator_eq_bot (isComponentOf_of_qs_normal hNJ hNn hq)
        hFsub with hNF | hNF
    · have hNe : N = quasithinGenFitting J :=
        eq_of_normal_qs hNF (fun m hm n hn => hNn m (hFJ hm) n hn) hq hqF
      rw [hNe]
      exact hlist
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hNF
      have hNF' : N ≤ quasithinGenFitting J :=
        (le_inf hNJ hNF).trans (centralizer_quasithinGenFitting_le J)
      exact not_le_centralizer_self_of_qs hq
        (hNF.trans (Subgroup.centralizer_le fun x hx => hNF' hx))
  ·
    exfalso
    obtain ⟨⟨e⟩, -, -⟩ := h2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact not_qs_of_le_solvable hNJ
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hq
  ·
    obtain ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ := h3
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_qs_normal hsup hc hNJ hNn hq with h | h
    · exact list_of_le_factor hf₁ h (fun g hg n hn => hNn g (hG₁J hg) n hn) hq
    · exact list_of_le_factor hf₂ h (fun g hg n hn => hNn g (hG₂J hg) n hn) hq
  ·
    obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, h3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
    have hMJ : G₁ ⊔ G₂ ≤ J := hJt ▸ le_sup_left
    have hG₁J : G₁ ≤ J := le_sup_left.trans hMJ
    obtain ⟨hp, -⟩ := qs_perfect_ne_bot hq
    have hNM : N ≤ G₁ ⊔ G₂ := by
      rw [← hp]
      exact (Subgroup.commutator_mono hNJ hNJ).trans
        (commutator_le_of_zpowers hJt (mem_normalizer_sup ht₁ ht₂))
    rcases le_or_le_of_qs_normal rfl hc hNM (fun x hx n hn => hNn x (hMJ hx) n hn) hq with
      h | h
    · have hs : IsSimpleGroup ↥G₁ :=
        @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e₁
      have hNe : N = G₁ := eq_of_normal_simple h (fun m hm n hn => hNn m (hG₁J hm) n hn) hq hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hNe).trans e₁⟩))))
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
      exact not_qs_of_le_solvable h inferInstance hq
  ·
    obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, hG₂⟩ := h5
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hL3 : ∀ {Gi : Subgroup (MulAut V)},
        (↥Gi ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) → Gi ≤ J → N ≤ Gi →
        B56QuasisimpleList ↥N := fun {Gi} e hGJ hNG => by
      have hs : IsSimpleGroup ↥Gi :=
        @MulEquiv.isSimpleGroup _ _ _ _
          (NQRigid.isSimpleGroup_statedSL_three_odd (F := ZMod 2) (m := 1)
            (by rw [Nat.card_zmod]; norm_num) (by decide)) e
      have hNe : N = Gi := eq_of_normal_simple hNG (fun m hm n hn => hNn m (hGJ hm) n hn) hq hs
      exact Or.inr (Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, by simp,
        ⟨(MulEquiv.subgroupCongr hNe).trans e⟩⟩)
    rcases le_or_le_of_qs_normal hsup hc hNJ hNn hq with h | h
    · exact hL3 e₁ hG₁J h
    · rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hπ⟩
      · exact hL3 e₂ hG₂J h
      · have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
        let e₂ := MulEquiv.ofBijective π ⟨hi, hπ.1⟩
        exact list_of_le_factor (Or.inl ⟨n, F, inferInstance, inferInstance,
          two_le_of_field hF, hF, ⟨e₂.symm⟩⟩) h (fun g hg n hn => hNn g (hG₂J hg) n hn) hq

end List

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem list_of_inYz (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) (hH : S.Hyp1367) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.IsQuasisimple ↥(S.plus K) ∧ B56QuasisimpleList ↥(S.plus K) := by
  have hF := hH.hF
  have hq := S.isQuasisimple_plus h1222 h517 hF hK hT
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hWT := (S.WK_le_Tv h1222 h517 hF hK.1 hT).1
  have hSQ := S.sqtkGroup_HK h1222 h517 hF hK.1 hT
  have hKJ := S.plus_le_jStar h1222 h517 hF hK hT
  have hJne : autOn (thompsonJ S.Tv) (S.WK K) ≠ ⊥ := by
    intro h
    have h1 := S.plus_eq_commutator h1222 h517 hF hK hT
    rw [h, Subgroup.commutator_bot_right] at h1
    exact (qs_perfect_ne_bot hq).2 h1.symm
  have hcases := b56Cases_jStar h56 hWT (S.Tv_le_HK K) hR hSQ hJne
  have hNn : ∀ x ∈ jStar (S.HK K) S.Tv (S.WK K), ∀ n ∈ S.plus K, x * n * x⁻¹ ∈ S.plus K :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp
      (S.HK_le_normalizer_plus h1222 h517 hF hK hT (jStar_le (S.Tv_le_HK K) hx)) n).mp hn
  exact ⟨hq, b56List_of_qs_normal hKJ hNn hq hcases⟩

end Setting

theorem list1367_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) : List1367 := by
  intro G _ _ T L V S hH K hK hT
  exact S.list_of_inYz h1222 h517 h56 hH hK hT

end CFSG.Quasithin.H13.A5
