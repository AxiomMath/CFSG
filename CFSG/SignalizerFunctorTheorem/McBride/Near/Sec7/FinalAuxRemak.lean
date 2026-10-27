module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAuxDefs

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

@[expose] def GrpCentreless (D : Type*) [Group D] : Prop :=
  ∀ z : D, (∀ x : D, Commute z x) → z = 1

@[expose] def GrpIndecomposable (D : Type*) [Group D] : Prop :=
  ∀ P Q : Subgroup D, (∀ x ∈ P, ∀ y ∈ Q, Commute x y) → P ⊓ Q = ⊥ → P ⊔ Q = ⊤ →
    P = ⊥ ∨ Q = ⊥

@[expose] def coordSub (ι D : Type*) [DecidableEq ι] [Group D] (k : ι) : Subgroup (ι → D) :=
  (MonoidHom.mulSingle (fun _ : ι => D) k).range

section Frobenius

variable {H : Type*} [Group H] {K V : Subgroup H}

private theorem exists_commutator_eq [Finite H] [K.Normal]
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1)
    {v : H} (hv : v ∈ V) (hv1 : v ≠ 1) {k : H} (hk : k ∈ K) :
    ∃ n ∈ K, n⁻¹ * v * n * v⁻¹ = k := by
  let f : K → K := fun n =>
    ⟨(n : H)⁻¹ * v * n * v⁻¹, by
      rw [show (n : H)⁻¹ * v * n * v⁻¹ = (n : H)⁻¹ * (v * n * v⁻¹) by group]
      exact mul_mem (inv_mem n.2) (Subgroup.Normal.conj_mem inferInstance (n : H) n.2 v)⟩
  have hinj : Function.Injective f := by
    intro n₁ n₂ h
    have h' : (n₁ : H)⁻¹ * v * n₁ = (n₂ : H)⁻¹ * v * n₂ :=
      mul_right_cancel (congrArg Subtype.val h)
    have hcomm : v * ((n₂ : H) * (n₁ : H)⁻¹) = ((n₂ : H) * (n₁ : H)⁻¹) * v := by
      calc v * ((n₂ : H) * (n₁ : H)⁻¹) = n₂ * ((n₂ : H)⁻¹ * v * n₂) * (n₁ : H)⁻¹ := by group
        _ = n₂ * ((n₁ : H)⁻¹ * v * n₁) * (n₁ : H)⁻¹ := by rw [h']
        _ = ((n₂ : H) * (n₁ : H)⁻¹) * v := by group
    have h1 := hfpf v hv hv1 _ (mul_mem n₂.2 (inv_mem n₁.2)) hcomm
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  obtain ⟨n, hn⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨k, hk⟩
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

private theorem exists_conj_of_not_mem [Finite H] [K.Normal]
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1) (hsup : K ⊔ V = ⊤) {m : H}
    (hm : m ∉ K) : ∃ n ∈ K, ∃ v ∈ V, v ≠ 1 ∧ n⁻¹ * v * n = m := by
  have hm' : m ∈ (↑(K ⊔ V) : Set H) := by rw [hsup]; trivial
  rw [Subgroup.normal_mul] at hm'
  obtain ⟨k, hk, v, hv, rfl⟩ := hm'
  have hv1 : v ≠ 1 := fun h => hm (by simpa [h] using hk)
  obtain ⟨n, hn, hnk⟩ := exists_commutator_eq hfpf hv hv1 hk
  exact ⟨n, hn, v, hv, hv1, by rw [← hnk]; group⟩

private theorem le_of_normal_not_le [Finite H] [K.Normal]
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1) (hsup : K ⊔ V = ⊤)
    {M : Subgroup H} [M.Normal] (hM : ¬ M ≤ K) : K ≤ M := by
  obtain ⟨m, hmM, hmK⟩ := IsConcreteLE.not_le_iff_exists.mp hM
  obtain ⟨n, hn, v, hv, hv1, rfl⟩ := exists_conj_of_not_mem hfpf hsup hmK
  have hvM : v ∈ M := by
    have := Subgroup.Normal.conj_mem inferInstance _ hmM n
    simpa [mul_assoc] using this
  intro k hk
  obtain ⟨n', hn', hk'⟩ := exists_commutator_eq hfpf hv hv1 hk
  rw [← hk']
  have h1 := Subgroup.Normal.conj_mem (inferInstance : M.Normal) v hvM n'⁻¹
  rw [inv_inv] at h1
  exact mul_mem h1 (inv_mem hvM)

private theorem grpCentreless_of_frobenius [Finite H] [K.Normal] (hK : K ≠ ⊥) (hV : V ≠ ⊥)
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1) (hsup : K ⊔ V = ⊤) :
    GrpCentreless H := by
  intro z hz
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  by_cases hzK : z ∈ K
  · exact hfpf v hvV hv1' z hzK (hz v).symm.eq
  · exfalso
    have hcen : K ≤ Subgroup.center H :=
      le_of_normal_not_le hfpf hsup fun h =>
        hzK (h (Subgroup.mem_center_iff.mpr fun g => (hz g).symm.eq))
    obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
    have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact hk1' (hfpf v hvV hv1' k hkK (Subgroup.mem_center_iff.mp (hcen hkK) v))

private theorem normal_of_commute_sup {P Q : Subgroup H} (hc : ∀ x ∈ P, ∀ y ∈ Q, Commute x y)
    (hs : P ⊔ Q = ⊤) : P.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hs]
  refine sup_le Subgroup.le_normalizer ?_
  rw [Subgroup.le_normalizer_iff]
  intro q hq x hx
  rw [← (hc x hx q hq).eq]
  simpa using hx

private theorem grpIndecomposable_of_frobenius [Finite H] [K.Normal] (hK : K ≠ ⊥) (hV : V ≠ ⊥)
    (hKV : K ⊓ V = ⊥) (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, v * k = k * v → k = 1)
    (hsup : K ⊔ V = ⊤) : GrpIndecomposable H := by
  intro P Q hc hPQ hs
  have hPn : P.Normal := normal_of_commute_sup hc hs
  have hQn : Q.Normal :=
    normal_of_commute_sup (fun x hx y hy => (hc y hy x hx).symm) (by rwa [sup_comm])
  by_cases hPK : P ≤ K <;> by_cases hQK : Q ≤ K
  · exfalso
    have hVK : V ≤ K := le_top.trans (hs.symm.le.trans (sup_le hPK hQK))
    exact hV (by rw [eq_bot_iff, ← hKV]; exact le_inf hVK le_rfl)
  · left
    have hKQ : K ≤ Q := le_of_normal_not_le hfpf hsup hQK
    rw [eq_bot_iff, ← hPQ]
    exact le_inf le_rfl (hPK.trans hKQ)
  · right
    have hKP : K ≤ P := le_of_normal_not_le hfpf hsup hPK
    rw [eq_bot_iff, ← hPQ]
    exact le_inf (hQK.trans hKP) le_rfl
  · exfalso
    have hKP : K ≤ P := le_of_normal_not_le hfpf hsup hPK
    have hKQ : K ≤ Q := le_of_normal_not_le hfpf hsup hQK
    exact hK (by rw [eq_bot_iff, ← hPQ]; exact le_inf hKP hKQ)

end Frobenius

theorem frobenius_props {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (hF : CFSG.SignalizerFunctorTheorem.McBride.IsFrobeniusWithKernel H K) :
    Nontrivial ↥H ∧ GrpCentreless ↥H ∧ GrpIndecomposable ↥H := by
  obtain ⟨hK0, hKH, hKn, V, hV0, hVH, hdisj, hsup, hfpf⟩ := hF
  have hK : K.subgroupOf H ≠ ⊥ := fun h =>
    hK0 (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h) hKH)
  have hV : V.subgroupOf H ≠ ⊥ := fun h =>
    hV0 (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h) hVH)
  have hKV : K.subgroupOf H ⊓ V.subgroupOf H = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (x : X) ∈ K ⊓ V := ⟨hx.1, hx.2⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hsup' : K.subgroupOf H ⊔ V.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKH hVH, hsup, Subgroup.subgroupOf_self]
  have hfpf' : ∀ v ∈ V.subgroupOf H, v ≠ 1 → ∀ k ∈ K.subgroupOf H, v * k = k * v → k = 1 := by
    intro v hv hv1 k hk hvk
    exact Subtype.ext (hfpf v hv (fun h => hv1 (Subtype.ext h)) k hk (congrArg Subtype.val hvk))
  have := hKn
  refine ⟨?_, grpCentreless_of_frobenius hK hV hfpf' hsup',
    grpIndecomposable_of_frobenius hK hV hKV hfpf' hsup'⟩
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  exact ⟨⟨(a : H), 1, fun h => ha (Subtype.ext h)⟩⟩

section Remak

private theorem exists_support_of_decomposition {D : Type*} [Group D] (hDc : GrpCentreless D)
    (hDi : GrpIndecomposable D) {ι : Type*} {Y Z : Subgroup (ι → D)}
    (hc : ∀ x ∈ Y, ∀ y ∈ Z, Commute x y) (hsup : Y ⊔ Z = ⊤) :
    ∃ J : Set ι, ∀ x : ι → D, x ∈ Y ↔ ∀ k, k ∉ J → x k = 1 := by
  have key : ∀ k : ι, Y.map (Pi.evalMonoidHom (fun _ : ι => D) k) = ⊥ ∨
      Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) = ⊥ := by
    intro k
    set e := Pi.evalMonoidHom (fun _ : ι => D) k
    have hc' : ∀ x ∈ Y.map e, ∀ y ∈ Z.map e, Commute x y := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrFun (hc a ha b hb).eq k
    have hsurj : Function.Surjective e := Function.surjective_eval k
    have hsup' : Y.map e ⊔ Z.map e = ⊤ := by
      rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective e hsurj]
    refine hDi _ _ hc' ?_ hsup'
    refine eq_bot_iff.mpr fun d hd => ?_
    rw [Subgroup.mem_bot]
    refine hDc d fun x => ?_
    have hle : (⊤ : Subgroup D) ≤ Subgroup.centralizer {d} := by
      rw [← hsup']
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc' a ha d hd.2).eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc' d hd.1 b hb).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x))).symm
  refine ⟨{k | Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) = ⊥}, fun x => ?_⟩
  have hY : ∀ y ∈ Y, ∀ k, Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) ≠ ⊥ → y k = 1 := by
    intro y hy k hk
    have hmem : y k ∈ Y.map (Pi.evalMonoidHom (fun _ : ι => D) k) := ⟨y, hy, rfl⟩
    rwa [(key k).resolve_right hk, Subgroup.mem_bot] at hmem
  have hZ : ∀ z ∈ Z, ∀ k, Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) = ⊥ → z k = 1 := by
    intro z hz k hk
    have hmem : z k ∈ Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) := ⟨z, hz, rfl⟩
    rwa [hk, Subgroup.mem_bot] at hmem
  constructor
  · intro hx k hk
    exact hY x hx k hk
  · intro hx
    have hZn : Z.Normal := normal_of_commute_sup (fun a ha b hb => (hc b hb a ha).symm)
      (by rwa [sup_comm])
    have hxs : x ∈ Y ⊔ Z := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxs
    have hz1 : z = 1 := by
      funext k
      by_cases hk : Z.map (Pi.evalMonoidHom (fun _ : ι => D) k) = ⊥
      · exact hZ z hz k hk
      · have h1 := hx k hk
        rw [Pi.mul_apply, hY y hy k hk, one_mul] at h1
        exact h1
    rw [hz1, mul_one]
    exact hy

private theorem exists_support_comap {G : Type*} [Group G] {D : Type*} [Group D]
    (hDc : GrpCentreless D) (hDi : GrpIndecomposable D) {ι : Type*} (Φ : (ι → D) →* G)
    (hΦ : Function.Injective Φ) {T : Subgroup G} (hT : Φ.range = T) {ℓ : Type*}
    {F : ℓ → Subgroup G} (hF : IsIDP F T) (l : ℓ) :
    ∃ J : Set ι, ∀ x : ι → D, x ∈ (F l).comap Φ ↔ ∀ k, k ∉ J → x k = 1 := by
  have hRT : (⨆ (j) (_ : j ≠ l), F j) ≤ T := iSup₂_le fun j _ => hF.le j
  have hFR : F l ⊔ (⨆ (j) (_ : j ≠ l), F j) = T := by
    rw [← hF.iSup_eq]
    exact (iSup_split_single F l).symm
  have hcomm : ∀ x ∈ F l, ∀ y ∈ (⨆ (j) (_ : j ≠ l), F j), Commute x y := by
    intro x hx y hy
    have hle : (⨆ (j) (_ : j ≠ l), F j) ≤ Subgroup.centralizer (F l : Set G) :=
      iSup₂_le fun j hj z hz =>
        Subgroup.mem_centralizer_iff.mpr fun h hh => (hF.commute l j (Ne.symm hj) h hh z hz).eq
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx
  refine exists_support_of_decomposition hDc hDi
    (Y := (F l).comap Φ) (Z := (⨆ (j) (_ : j ≠ l), F j).comap Φ) ?_ ?_
  · intro x hx y hy
    exact hΦ (by rw [map_mul, map_mul]; exact (hcomm _ hx _ hy).eq)
  · rw [Subgroup.comap_sup_eq_of_le_range Φ (hT ▸ hF.le l) (hT ▸ hRT), hFR, ← hT,
      MonoidHom.comap_range_self]

private theorem exists_equiv_of_partition {ι ℓ : Type*} [Finite ι] [Finite ℓ] (J : ℓ → Set ι)
    (hne : ∀ l, (J l).Nonempty) (hdis : ∀ l l', l ≠ l' → Disjoint (J l) (J l'))
    (hcov : ∀ k, ∃ l, k ∈ J l) (hcard : Nat.card ℓ = Nat.card ι) :
    ∃ e : ℓ ≃ ι, ∀ l, J l = {e l} := by
  choose c hc using hcov
  have huniq : ∀ k l, k ∈ J l → c k = l := by
    intro k l hk
    by_contra hne'
    exact Set.disjoint_left.mp (hdis _ _ hne') (hc k) hk
  have hsurj : Function.Surjective c := fun l => by
    obtain ⟨k, hk⟩ := hne l
    exact ⟨k, huniq k l hk⟩
  have hbij : Function.Bijective c := hsurj.bijective_of_nat_card_le hcard.symm.le
  refine ⟨(Equiv.ofBijective c hbij).symm, fun l => ?_⟩
  ext k
  rw [Set.mem_singleton_iff, Equiv.eq_symm_apply]
  exact ⟨fun hk => huniq k l hk, fun hk => hk ▸ hc k⟩

end Remak

theorem exists_equiv_coordSub {G : Type*} [Group G] {D : Type*} [Group D] [Nontrivial D]
    (hDc : GrpCentreless D) (hDi : GrpIndecomposable D)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : (ι → D) →* G) (hΦ : Function.Injective Φ)
    {T : Subgroup G} (hT : Φ.range = T) {ℓ : Type*} [Finite ℓ] (F : ℓ → Subgroup G)
    (hF : IsIDP F T) (hne : ∀ l, F l ≠ ⊥) (hcard : Nat.card ℓ = Fintype.card ι) :
    ∃ e : ℓ ≃ ι, ∀ l, F l = (coordSub ι D (e l)).map Φ := by
  choose J hJ using fun l => exists_support_comap hDc hDi Φ hΦ hT hF l
  have hFT : ∀ l, F l ≤ Φ.range := fun l => hT ▸ hF.le l
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  have hnon : ∀ l, (J l).Nonempty := by
    intro l
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    refine hne l (eq_bot_iff.mpr fun f hf => ?_)
    obtain ⟨x, rfl⟩ := hFT l hf
    have hx : x = 1 := funext fun k => (hJ l x).mp hf k (by simp [hcon])
    rw [hx, map_one]
    exact one_mem _
  have hsingle : ∀ l k, k ∈ J l → Pi.mulSingle k d ∈ (F l).comap Φ := by
    intro l k hk
    rw [hJ]
    intro k' hk'
    have hkk : k' ≠ k := fun h => hk' (h ▸ hk)
    simp [hkk]
  have hdis : ∀ l l', l ≠ l' → Disjoint (J l) (J l') := by
    intro l l' hll'
    rw [Set.disjoint_left]
    intro k hk hk'
    have h1 : Φ (Pi.mulSingle k d) ∈ F l ⊓ F l' := ⟨hsingle l k hk, hsingle l' k hk'⟩
    rw [hF.inf_eq_bot hll', Subgroup.mem_bot] at h1
    have h2 : Pi.mulSingle k d = 1 := hΦ (by rw [h1, map_one])
    exact hd (by simpa using congrFun h2 k)
  have hcov : ∀ k, ∃ l, k ∈ J l := by
    intro k
    by_contra hcon
    have hS : ∀ l, F l ≤ (MonoidHom.ker (Pi.evalMonoidHom (fun _ : ι => D) k)).map Φ := by
      intro l f hf
      obtain ⟨x, rfl⟩ := hFT l hf
      exact ⟨x, (hJ l x).mp hf k fun hk => hcon ⟨l, hk⟩, rfl⟩
    have hTS : T ≤ (MonoidHom.ker (Pi.evalMonoidHom (fun _ : ι => D) k)).map Φ := by
      rw [← hF.iSup_eq]
      exact iSup_le hS
    have hmem : Φ (Pi.mulSingle k d) ∈ T := hT ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hTS hmem
    have hyd : y = Pi.mulSingle k d := hΦ hy'
    exact hd (by simpa [hyd] using hy)
  obtain ⟨e, he⟩ := exists_equiv_of_partition J hnon hdis hcov
    (by rw [hcard, Nat.card_eq_fintype_card])
  refine ⟨e, fun l => ?_⟩
  have h1 : (F l).comap Φ = coordSub ι D (e l) := by
    ext x
    rw [hJ]
    constructor
    · intro hx
      refine ⟨x (e l), ?_⟩
      funext k
      by_cases hk : k = e l
      · subst hk
        simp
      · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hk]
        exact (hx k (by simp [he, hk])).symm
    · rintro ⟨y, rfl⟩ k hk
      have hk' : k ≠ e l := by simpa [he] using hk
      simp [hk']
  rw [← h1, Subgroup.map_comap_eq_self (hFT l)]

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
