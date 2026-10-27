module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKF135
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r5e_mem_normalizer_of_conj {G : Type*} [Group G] {g : G} {H : Subgroup G}
    (h1 : ∀ y ∈ H, g * y * g⁻¹ ∈ H) (h2 : ∀ y ∈ H, g⁻¹ * y * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  have h3 := h2 _ hh
  rwa [e] at h3

theorem r5e_isPGroup_of_exp {G : Type*} [Group G] {p : ℕ} (H : Subgroup G)
    (h : ∀ x ∈ H, x ^ p = 1) : IsPGroup p H := by
  unfold IsPGroup
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using h g.1 g.2)

theorem r5e_isPGroup_of_pow {G : Type*} [Group G] {q : ℕ} (H : Subgroup G)
    (h : ∀ y ∈ H, ∃ k : ℕ, y ^ q ^ k = 1) : IsPGroup q H := by
  unfold IsPGroup
  intro g
  obtain ⟨k, hk⟩ := h g.1 g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem r5e_pow_map {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G) {q : ℕ}
    (h : ∀ n ∈ K, ∃ k : ℕ, n ^ q ^ k = 1) : ∀ y ∈ K.map f, ∃ k : ℕ, y ^ q ^ k = 1 := by
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨k, hk⟩ := h n hn
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem r5e_map_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    {n : G} (hn : ∀ m ∈ K, n * m * n⁻¹ ∈ K) (hn' : ∀ m ∈ K, n⁻¹ * m * n ∈ K) :
    f n ∈ Subgroup.normalizer ((K.map f : Subgroup H) : Set H) := by
  apply r5e_mem_normalizer_of_conj
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨n * m * n⁻¹, hn m hm, by simp [map_mul, map_inv]⟩
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨n⁻¹ * m * n, hn' m hm, by simp [map_mul, map_inv]⟩

theorem r5e_actS_normalizes {M' : Type*} [Group M'] (J H : Subgroup M')
    (n : Subgroup.normalizer (J : Set M')) (hn : (n : M') ∈ Subgroup.normalizer (H : Set M')) :
    actS J n ∈ Subgroup.normalizer
      (((H.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J) :
        Subgroup (MulAut (J ⧸ Subgroup.center J))) : Set (MulAut (J ⧸ Subgroup.center J))) := by
  apply r5e_map_normalizer
  · intro m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have h := (Subgroup.mem_normalizer_iff.mp hn (m : M')).mp hm
    simpa using h
  · intro m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have h := (Subgroup.mem_normalizer_iff''.mp hn (m : M')).mp hm
    simpa using h

theorem r5e_card {M' : Type*} [Group M'] {J : Subgroup M'} (hJ : Group.IsPerfect J)
    {Ē : Subgroup M'} (hĒN : Ē ≤ Subgroup.normalizer (J : Set M')) :
    Nat.card ((Ē.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J)) =
      (Subgroup.centralizer (J : Set M') ⊓ Ē).relIndex Ē := by
  have hk := Subgroup.relIndex_ker (f := actS J)
    (K := Ē.subgroupOf (Subgroup.normalizer (J : Set M')))
  have hker : (actS J).ker =
      (Subgroup.centralizer (J : Set M')).subgroupOf (Subgroup.normalizer (J : Set M')) := by
    ext n
    rw [MonoidHom.mem_ker, actS_eq_one_iff hJ n, Subgroup.mem_subgroupOf]
  rw [hker, Subgroup.relIndex_subgroupOf hĒN] at hk
  have h2 := Subgroup.relIndex_inf_mul_relIndex (H := Subgroup.centralizer (J : Set M'))
    (K := Ē) (L := Ē)
  rw [inf_idem, Subgroup.relIndex_self, mul_one] at h2
  rw [← hk, h2]

theorem r5e_exists_comm {M' : Type*} [Group M'] {J Ū Eu : Subgroup M'}
    (hcomm : Ū ≤ ⁅Ū, Eu⁆ ⊔ Subgroup.centralizer (J : Set M'))
    (hŪne : ¬ Ū ≤ Subgroup.centralizer (J : Set M')) :
    ∃ u ∈ Ū, ∃ f ∈ Eu, ⁅u, f⁆ ∉ Subgroup.centralizer (J : Set M') := by
  by_contra hcon
  push Not at hcon
  apply hŪne
  have hle : ⁅Ū, Eu⁆ ≤ Subgroup.centralizer (J : Set M') := Subgroup.commutator_le.mpr hcon
  exact hcomm.trans (sup_le hle le_rfl)

theorem r5e_xV {M' : Type} [Group M'] [Finite M'] (J : Subgroup M') (hperf : Group.IsPerfect J)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (Ē Eu Ū : Subgroup M')
    (hĒexp : ∀ e ∈ Ē, e ^ p = 1) (hĒN : Ē ≤ Subgroup.normalizer (J : Set M'))
    (hŪN : Ū ≤ Subgroup.normalizer (J : Set M')) (hŪ2 : IsPGroup 2 Ū)
    (hŪne : ¬ Ū ≤ Subgroup.centralizer (J : Set M'))
    (hEuĒ : Eu ≤ Ē) (hŪEu : Eu ≤ Subgroup.normalizer (Ū : Set M'))
    (hcomm : Ū ≤ ⁅Ū, Eu⁆ ⊔ Subgroup.centralizer (J : Set M')) :
    ∃ nf : Subgroup.normalizer (J : Set M'), (nf : M') ∈ Eu ∧ actS J nf ≠ 1 ∧
      orderOf (actS J nf) = p ∧
      ∃ V : Subgroup (MulAut (J ⧸ Subgroup.center J)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        (∀ v ∈ V, actS J nf * v * (actS J nf)⁻¹ ∈ V) ∧
        ⁅V, Subgroup.zpowers (actS J nf)⁆ = V := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u₀, hu₀, f, hf, hcf⟩ := r5e_exists_comm hcomm hŪne
  have hfĒ : f ∈ Ē := hEuĒ hf
  have hfN : f ∈ Subgroup.normalizer (J : Set M') := hĒN hfĒ
  have hu₀N : u₀ ∈ Subgroup.normalizer (J : Set M') := hŪN hu₀
  have hc : ⁅u₀, f⁆ ∈ Subgroup.normalizer (J : Set M') := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu₀N hfN) (inv_mem hu₀N)) (inv_mem hfN)
  obtain ⟨nf, hnf⟩ : ∃ n : Subgroup.normalizer (J : Set M'), (n : M') = f :=
    ⟨⟨f, hfN⟩, rfl⟩
  obtain ⟨nu, hnu⟩ : ∃ n : Subgroup.normalizer (J : Set M'), (n : M') = u₀ :=
    ⟨⟨u₀, hu₀N⟩, rfl⟩
  obtain ⟨nc, hnc⟩ : ∃ n : Subgroup.normalizer (J : Set M'), (n : M') = ⁅u₀, f⁆ :=
    ⟨⟨⁅u₀, f⁆, hc⟩, rfl⟩
  have e : nc = nu * nf * nu⁻¹ * nf⁻¹ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnc, hnu, hnf, commutatorElement_def])
  have hcomm_eq : ⁅actS J nu, actS J nf⁆ = actS J nc := by
    simp only [e, map_mul, map_inv, commutatorElement_def]
  have hne : ⁅actS J nu, actS J nf⁆ ≠ 1 := by
    rw [hcomm_eq]
    intro h
    apply hcf
    have h' := (actS_eq_one_iff hperf nc).mp h
    rw [hnc] at h'
    exact h'
  have hx_ne : actS J nf ≠ 1 := by
    intro h
    apply hne
    rw [h, commutatorElement_one_right]
  have hnfE : (nf : M') ∈ Eu := by
    rw [hnf]
    exact hf
  have hxpow : actS J nf ^ p = 1 := by
    have hnE : (nf : M') ^ p = 1 := by
      rw [hnf]
      exact hĒexp f hfĒ
    have hn1 : nf ^ p = 1 := Subtype.ext (by simpa using hnE)
    rw [← map_pow, hn1, map_one]
  have hxorder : orderOf (actS J nf) = p := orderOf_eq_prime hxpow hx_ne
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      V₀ = (Ū.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J) := ⟨_, rfl⟩
  have hv₀ : actS J nu ∈ V₀ := by
    rw [hV₀]
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.mem_subgroupOf, hnu]
    exact hu₀
  have key : ∀ n ∈ Ū.subgroupOf (Subgroup.normalizer (J : Set M')), ∃ k : ℕ, n ^ 2 ^ k = 1 := by
    intro n hn
    obtain ⟨k, hk⟩ := hŪ2 ⟨(n : M'), Subgroup.mem_subgroupOf.mp hn⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h := congrArg Subtype.val hk
    simpa using h
  have hpow₀ : ∀ y ∈ V₀, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    rw [hV₀]
    exact r5e_pow_map (actS J) _ key
  have hV₀2 : IsPGroup 2 V₀ := r5e_isPGroup_of_pow _ hpow₀
  have hX : ¬ p ∣ Nat.card V₀ := by
    intro hdiv
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀2
    rw [hm] at hdiv
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hxN : actS J nf ∈ Subgroup.normalizer (V₀ : Set (MulAut (J ⧸ Subgroup.center J))) := by
    rw [hV₀]
    exact r5e_actS_normalizes J Ū nf (hŪEu hnfE)
  have hzp : Subgroup.zpowers (actS J nf) ≤
      Subgroup.normalizer (V₀ : Set (MulAut (J ⧸ Subgroup.center J))) :=
    Subgroup.zpowers_le.mpr hxN
  have hVsub : ⁅V₀, Subgroup.zpowers (actS J nf)⁆ ≤ V₀ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_le_of_le_normalizer hzp
  have hzpP : IsPGroup p (Subgroup.zpowers (actS J nf)) :=
    IsPGroup.of_card ((Nat.card_zpowers (actS J nf)).trans (hxorder.trans (pow_one p).symm))
  have hVx : ⁅⁅V₀, Subgroup.zpowers (actS J nf)⁆, Subgroup.zpowers (actS J nf)⁆ =
      ⁅V₀, Subgroup.zpowers (actS J nf)⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hzpP hzp hX
  have hVne : ⁅V₀, Subgroup.zpowers (actS J nf)⁆ ≠ ⊥ := by
    intro h
    have hmem := Subgroup.commutator_mem_commutator hv₀ (Subgroup.mem_zpowers (actS J nf))
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  have hV2 : IsPGroup 2 (⁅V₀, Subgroup.zpowers (actS J nf)⁆ :
      Subgroup (MulAut (J ⧸ Subgroup.center J))) :=
    r5e_isPGroup_of_pow _ (fun y hy => hpow₀ y (hVsub hy))
  have hxV : ∀ v ∈ (⁅V₀, Subgroup.zpowers (actS J nf)⁆ : Subgroup (MulAut (J ⧸ Subgroup.center J))),
      actS J nf * v * (actS J nf)⁻¹ ∈ ⁅V₀, Subgroup.zpowers (actS J nf)⁆ := by
    intro v hv
    refine r5gl_commutator_conj (g := actS J nf) ?_ ?_ hv
    · intro y hy
      exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(Commute.self_zpow (actS J nf) k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  exact ⟨nf, hnfE, hx_ne, hxorder, ⁅V₀, Subgroup.zpowers (actS J nf)⁆, hVne, hV2, hxV, hVx⟩

theorem identified_of_kf135 (hKF : KF135) {M' : Type} [Group M'] [Finite M'] (J : Subgroup M')
    (hJq : CFSG.IsQuasisimple J) (hList : Sec4.Census.List42 (J ⧸ Subgroup.center J))
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (Ē Eu Ū : Subgroup M') (ū : M')
    (hĒp : IsPGroup p Ē) (hĒexp : ∀ e ∈ Ē, e ^ p = 1)
    (hĒN : Ē ≤ Subgroup.normalizer (J : Set M'))
    (hidx : p ^ 3 ≤ (Subgroup.centralizer (J : Set M') ⊓ Ē).relIndex Ē)
    (hūN : ū ∈ Subgroup.normalizer (J : Set M')) (hū2 : ū * ū = 1)
    (hŪN : Ū ≤ Subgroup.normalizer (J : Set M')) (hŪ2 : IsPGroup 2 Ū)
    (hŪne : ¬ Ū ≤ Subgroup.centralizer (J : Set M'))
    (hūnc : ū ∉ Subgroup.centralizer (J : Set M'))
    (hEuĒ : Eu ≤ Ē) (hEuc : Eu ≤ Subgroup.centralizer ({ū} : Set M'))
    (hŪEu : Eu ≤ Subgroup.normalizer (Ū : Set M'))
    (hcomm : Ū ≤ ⁅Ū, Eu⁆ ⊔ Subgroup.centralizer (J : Set M'))
    (hH2a : ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      F ≤ (MulAut.conj : (J ⧸ Subgroup.center J) →* MulAut (J ⧸ Subgroup.center J)).range →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T)
    (hH2b : ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      F ≤ (Ē.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J) →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T) :
    Identified p (J ⧸ Subgroup.center J) := by
  have hperf : Group.IsPerfect J := hJq.1
  have hSsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hJq.2.1
  have hSnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := hJq.2.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0, hP0⟩ : ∃ P0 : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      P0 = (Ē.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J) := ⟨_, rfl⟩
  have hPexp : ∀ y ∈ P0, y ^ p = 1 := by
    rw [hP0]
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnE : (n : M') ^ p = 1 := hĒexp _ (Subgroup.mem_subgroupOf.mp hn)
    have hn1 : n ^ p = 1 := Subtype.ext (by simpa using hnE)
    rw [← map_pow, hn1, map_one]
  have hPp : IsPGroup p P0 := r5e_isPGroup_of_exp _ hPexp
  have hP3 : p ^ 3 ≤ Nat.card P0 := by
    rw [hP0, r5e_card hperf hĒN]
    exact hidx
  obtain ⟨nf, hnfEu, hxne, hxorder, V, hVne, hV2, hxV, hVx⟩ :=
    r5e_xV J hperf hp hp7 Ē Eu Ū hĒexp hĒN hŪN hŪ2 hŪne hEuĒ hŪEu hcomm
  have hxP : actS J nf ∈ P0 := by
    rw [hP0]
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.mem_subgroupOf]
    exact hEuĒ hnfEu
  have hsq : (⟨ū, hūN⟩ : Subgroup.normalizer (J : Set M')) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using hū2)
  have hū₀ne : actS J ⟨ū, hūN⟩ ≠ 1 := fun h => hūnc ((actS_eq_one_iff hperf ⟨ū, hūN⟩).mp h)
  have hū₀two : ∃ k : ℕ, actS J ⟨ū, hūN⟩ ^ 2 ^ k = 1 := by
    refine ⟨1, ?_⟩
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, ← map_pow, hsq, map_one]
  have hcomm_u : (⟨ū, hūN⟩ : Subgroup.normalizer (J : Set M')) * nf = nf * ⟨ū, hūN⟩ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp (hEuc hnfEu) ū (Set.mem_singleton ū))
  have hū₀x : actS J ⟨ū, hūN⟩ * actS J nf = actS J nf * actS J ⟨ū, hūN⟩ := by
    rw [← map_mul, ← map_mul, hcomm_u]
  have hH2b' : ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)), F ≤ P0 →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T := by
    rw [hP0]
    exact hH2b
  exact hKF (J ⧸ Subgroup.center J) hSsimple hSnonab hList p hp hp7 P0 hPp hP3 hPexp
    (actS J nf) hxP hxorder (actS J ⟨ū, hūN⟩) hū₀ne hū₀two hū₀x
    V hVne hV2 hxV hVx hH2a hH2b'

end CFSG.RankThree.PartTwo.Sec13.F135Last
