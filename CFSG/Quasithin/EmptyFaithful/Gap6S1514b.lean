module

public import CFSG.Quasithin.EmptyFaithful.Gap6S1514
public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_le_gap6 {T K : Subgroup G} (hT : quasithinIsSylowTwo T) (hTK : T ≤ K) :
    IsSylowTwoOf T K :=
  ⟨hTK, hT.1, fun hd => hT.2 (dvd_trans hd (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTK))⟩

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_gap6 (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ t ∈ Subgroup.normalizer (J : Set G), ∀ c ∈ Subgroup.centralizer (J : Set G),
      t * c * t⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
    intro t ht c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro j hj
    have hj' : t⁻¹ * j * t ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) j).mp hj
      simpa using this
    have h1 := hc _ hj'
    calc j * (t * c * t⁻¹) = t * ((t⁻¹ * j * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * j * t)) * t⁻¹ := by rw [h1]
      _ = (t * c * t⁻¹) * j := by group
  intro c
  refine ⟨key t ht c, fun hc => ?_⟩
  have := key t⁻¹ (Subgroup.inv_mem _ ht) _ hc
  simpa [mul_assoc] using this

@[expose] def Step1514GenResidual2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1519Concl T Mc M →
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ¬ oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ∀ K : Subgroup G, T ≤ K → K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      ¬ oTwoUpper K ≤ Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer
        (thompsonJi T 1 : Set G) : Subgroup G) : Set G) →
      (∀ L : Subgroup G, T ≤ L → L < K → oTwoUpper L ≤ Subgroup.centralizer
        ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G)) →
      ¬ K ≤ Subgroup.normalizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
      ¬ K ⊓ Subgroup.normalizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) ≤ M →
      ¬ Case3bOf T Mc M →
      ∃ H : Subgroup G, IsHStar T M H ∧
        H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        ¬ oTwoUpper H ≤ oTwoUpper (Subgroup.centralizer ((V154 T Mc M ⊓
          Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G))

theorem step1514GenResidual_of_residual2 (h159 : StageLemma1519) (hRes : Step1514GenResidual2) :
    Step1514GenResidual := by
  intro G _ _ T Mc M h hMf hCE hyp1 hyp2 K hTK hKC hK hmin hA hnb
  have hL : Lemma1519Concl T Mc M := h159 G T Mc M h hMf hCE
  set W : Subgroup G := V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) with hW
  set CW : Subgroup G := Subgroup.centralizer (W : Set G) with hCW
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTM : T ≤ M := hMf.1.1.2
  have hKM : ¬ K ≤ M := fun hKM => hK ((oTwoUpper_mono (le_inf hKM hKC)).trans hyp1)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    have h1 : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans (le_normalizer_V154 T Mc M)
    have h2 : T ≤ Subgroup.normalizer (Subgroup.centralizer (thompsonJi T 1 : Set G) : Set G) :=
      fun x hx => normalizer_le_normalizer_centralizer_gap6 _
        (normalizer_le_normalizer_thompsonJi151 T 1 (Subgroup.le_normalizer hx))
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1 hx, h2 hx⟩
  have hL2 : ∀ L : Subgroup G, T ≤ L → L < K → L ≤ Subgroup.normalizer (W : Set G) := by
    intro L hTL hLK
    have hLsyl := isSylowTwoOf_of_le_gap6 h.sylow hTL
    exact (eq_oTwoUpper_sup_of_isSylowTwoOf hLsyl).le.trans
      (sup_le ((hmin L hTL hLK).trans (Subgroup.centralizer_le_normalizer (W : Set G))) hTW)
  have hKW : ¬ K ≤ Subgroup.normalizer (W : Set G) := by
    intro hKN
    have hZT : quasithinOmegaOneCenter T ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
    have hT1 : T ≠ ⊥ := fun hbot => h.omegaOneCenter_ne_bot (le_bot_iff.mp (hZT.trans hbot.le))
    have hJM : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
      (S1414.normalizer_thompsonJ_le_CGS hT2 hT1).trans hL.one_cgs
    set C : Subgroup G := K ⊓ CW with hC
    have hJK : thompsonJ T ≤ K := (C1GN.thompsonJ_le T).trans hTK
    have hJCW : thompsonJ T ≤ CW := by
      have h1 : thompsonJ T ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
        Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL.one_commute)
      exact h1.trans (Subgroup.centralizer_le fun x hx => hx.1)
    have hJC : thompsonJ T ≤ C := le_inf hJK hJCW
    have hKCn : K ≤ Subgroup.normalizer (C : Set G) := by
      have key : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
        intro k hk c hc
        refine ⟨K.mul_mem (K.mul_mem hk hc.1) (K.inv_mem hk), ?_⟩
        show k * c * k⁻¹ ∈ Subgroup.centralizer (W : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw' : k⁻¹ * w * k ∈ W := by
          have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) w).mp hw
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hw'
        calc w * (k * c * k⁻¹) = k * ((k⁻¹ * w * k) * c) * k⁻¹ := by group
          _ = k * (c * (k⁻¹ * w * k)) * k⁻¹ := by rw [h1]
          _ = (k * c * k⁻¹) * w := by group
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => key k hk c hc, fun hc => ?_⟩
      have := key k⁻¹ (K.inv_mem hk) _ hc
      simpa [mul_assoc] using this
    have hTsyl : IsSylowTwoOf T K := isSylowTwoOf_of_le_gap6 h.sylow hTK
    have hdec := S1414.frattini_decomp hTsyl (inf_le_left : C ≤ K) hKCn hJC
    set K₂ : Subgroup G := K ⊓ Subgroup.normalizer (thompsonJ T : Set G) with hK₂
    by_cases hK2 : K ≤ Subgroup.normalizer (thompsonJ T : Set G)
    · exact hKM (hK2.trans hJM)
    · have hTK₂ : T ≤ K₂ := le_inf hTK fun x hx =>
        normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer hx)
      have hlt : K₂ < K := lt_of_le_of_ne inf_le_left fun h' =>
        hK2 (h' ▸ inf_le_right)
      have hK₂O : oTwoUpper K₂ ≤ CW := hmin K₂ hTK₂ hlt
      have hK₂syl := isSylowTwoOf_of_le_gap6 h.sylow hTK₂
      have hK₂eq := eq_oTwoUpper_sup_of_isSylowTwoOf hK₂syl
      apply hK
      refine oTwoUpper_le_of_pow_mem fun x hx => ?_
      obtain ⟨n, hn, y, hy, rfl⟩ := hdec x hx
      have hy' : y ∈ oTwoUpper K₂ ⊔ T := hK₂eq ▸ hy
      have hTn : T ≤ Subgroup.normalizer (oTwoUpper K₂ : Set G) :=
        hTK₂.trans (le_normalizer_oTwoUpper K₂)
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper K₂) T hTn] at hy'
      obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.mp hy'
      have huC : u ∈ C := ⟨(oTwoUpper_le K₂ hu).1, hK₂O hu⟩
      obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
      have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have htN : t ∈ Subgroup.normalizer (C : Set G) := hKCn (hTK ht)
      obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq (C.mul_mem hn huC) htN (2 ^ k)
      refine ⟨k, ?_⟩
      have e : n * (u * t) = (n * u) * t := by group
      rw [e, hxe, htk, mul_one]
      exact hx'.2
  obtain ⟨L, hTL, hLK, hLM⟩ := hA
  have hK1M : ¬ K ⊓ Subgroup.normalizer (W : Set G) ≤ M := fun hle =>
    hLM ((le_inf hLK.le (hL2 L hTL hLK)).trans hle)
  exact hRes G T Mc M h hMf hCE hL hyp1 hyp2 K hTK hKC hK hmin hKW hK1M hnb

theorem step1514Gen_of_residual2 (h159 : StageLemma1519) (hRes : Step1514GenResidual2) :
    Step1514Gen :=
  step1514Gen_of_residual (step1514GenResidual_of_residual2 h159 hRes)

end Gap6

end CFSG.Quasithin
