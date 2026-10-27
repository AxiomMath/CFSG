module

public import CFSG.RankThree.PartOne.KF.HeartMod
public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

theorem heartCtx_of_symCtx {M P : Type} [Group M] [Group P] (π : M →* P)
    (hπ : Function.Surjective π) {T : Subgroup M} (SM : SymCtx 5 5 K (⊤ : Subgroup M) T)
    (hker_le : π.ker ≤ T)
    (hZV : ∀ d : torusVec 5 5 K, π ((SM.tor d : T) : M) = 1 ↔ d ∈ scalarSub 5 5 K) :
    Nonempty (WCtx (heartAct K) (⊤ : Subgroup P) (T.map π)) := by
  classical
  have hlift : ∀ x : M, π x ∈ T.map π → x ∈ T := by
    rintro x ⟨t, ht, htx⟩
    have h1 : t⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htx, inv_mul_cancel]
    have h2 : x = t * (t⁻¹ * x) := by group
    rw [h2]
    exact T.mul_mem ht (hker_le h1)
  let φ : torusVec 5 5 K →* ↥(T.map π) :=
    { toFun := fun d => ⟨π ((SM.tor d : T) : M), ⟨((SM.tor d : T) : M), (SM.tor d).2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun d e => by
        apply Subtype.ext
        simp [map_mul] }
  have hφ1 : ∀ d, φ d = 1 ↔ d ∈ scalarSub 5 5 K := fun d => by
    rw [← hZV d]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hle : scalarSub 5 5 K ≤ φ.ker := fun d hd => (hφ1 d).mpr hd
  let φ' : Heart K →* ↥(T.map π) := QuotientGroup.lift (scalarSub 5 5 K) φ hle
  have hφ'mk : ∀ d, φ' (heartMk d) = φ d := fun d => rfl
  have hinj : Function.Injective φ' := by
    intro x y hxy
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    obtain ⟨e, rfl⟩ := heartMk_surjective y
    rw [hφ'mk, hφ'mk] at hxy
    have h1 : φ (d⁻¹ * e) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := (hφ1 _).mp h1
    show (QuotientGroup.mk d : Heart K) = QuotientGroup.mk e
    rw [QuotientGroup.eq]
    exact h2
  have hsurj : Function.Surjective φ' := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨d, hd⟩ := SM.tor.surjective ⟨t, ht⟩
    refine ⟨heartMk d, ?_⟩
    rw [hφ'mk]
    apply Subtype.ext
    show π ((SM.tor d : T) : M) = π t
    rw [hd]
  let tor : Heart K ≃* ↥(T.map π) := MulEquiv.ofBijective φ' ⟨hinj, hsurj⟩
  have htor_mk : ∀ d, ((tor (heartMk d) : ↥(T.map π)) : P) = π ((SM.tor d : T) : M) :=
    fun d => rfl
  have hnorm : ∀ g : M, g ∈ Subgroup.normalizer (T : Set M) ↔
      π g ∈ Subgroup.normalizer ((T.map π : Subgroup P) : Set P) := by
    intro g
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨g * t * g⁻¹, (h t).mp ht, by simp⟩
      · intro hx
        obtain ⟨y, rfl⟩ := hπ x
        have h1 : π (g * y * g⁻¹) ∈ T.map π := by simpa using hx
        exact ⟨y, (h y).mpr (hlift _ h1), rfl⟩
    · intro h y
      constructor
      · intro hy
        have h1 := (h (π y)).mp ⟨y, hy, rfl⟩
        exact hlift _ (by simpa using h1)
      · intro hy
        have h1 : π g * π y * (π g)⁻¹ ∈ T.map π := by simpa using (⟨_, hy, rfl⟩ : _ ∈ T.map π)
        exact hlift _ ((h (π y)).mpr h1)
  have hact : ∀ (g : M) (hg : g ∈ Subgroup.normalizer (T : Set M)) (σ : Equiv.Perm (Fin 5)),
      T.normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr SM.tor (symAut 5 K σ) →
      (T.map π).normalizerMonoidHom ⟨π g, (hnorm g).mp hg⟩ = MulAut.congr tor (heartAct K σ) := by
    intro g hg σ hgσ
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := tor.surjective x
    obtain ⟨d, rfl⟩ := heartMk_surjective y
    rw [SymCtx.congr_apply_tor, heartAct_mk]
    apply Subtype.ext
    have h1 := congrArg (fun y : T => ((y : T) : M)) (DFunLike.congr_fun hgσ (SM.tor d))
    simp only [SymCtx.congr_apply_tor, symAut_apply] at h1
    show π g * ((tor (heartMk d) : ↥(T.map π)) : P) * (π g)⁻¹ = _
    rw [htor_mk]
    show π g * π ((SM.tor d : T) : M) * (π g)⁻¹ = π ((SM.tor (symAct 5 K σ d) : T) : M)
    rw [← h1]
    show _ = π (g * ((SM.tor d : T) : M) * g⁻¹)
    simp
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · intro σ
    obtain ⟨g, hg, -, hgσ⟩ := SM.exists_elt σ
    exact ⟨π g, (hnorm g).mp hg, Subgroup.mem_top _, hact g hg σ hgσ⟩
  · intro g' hg' _
    obtain ⟨g, rfl⟩ := hπ g'
    have hg : g ∈ Subgroup.normalizer (T : Set M) := (hnorm g).mpr hg'
    obtain ⟨σ, hgσ⟩ := SM.induced g hg (Subgroup.mem_top _)
    exact ⟨σ, hact g hg σ hgσ⟩

theorem symCtx_scalars [Finite K] {M : Type} [Group M] {T : Subgroup M}
    (SM : SymCtx 5 5 K (⊤ : Subgroup M) T) (Zc : Subgroup M) (hZc : Zc ≤ Subgroup.center M)
    (hZT : Zc ≤ T) (hZcard : Nat.card Zc = 5) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    (d : torusVec 5 5 K) : ((SM.tor d : T) : M) ∈ Zc ↔ d ∈ scalarSub 5 5 K := by
  classical
  have hfwd : ∀ d : torusVec 5 5 K, ((SM.tor d : T) : M) ∈ Zc → d ∈ scalarSub 5 5 K := by
    intro d hd i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨g, hg, -, hgσ⟩ := SM.exists_elt (Equiv.swap i j)
      have h1 := congrArg (fun y : T => ((y : T) : M)) (DFunLike.congr_fun hgσ (SM.tor d))
      simp only [SymCtx.congr_apply_tor, symAut_apply] at h1
      have h2 : g * ((SM.tor d : T) : M) * g⁻¹ = ((SM.tor d : T) : M) := by
        have := Subgroup.mem_center_iff.mp (hZc hd) g
        rw [this]
        group
      have h3 : SM.tor (symAct 5 K (Equiv.swap i j) d) = SM.tor d := by
        apply Subtype.ext
        rw [← h1]
        exact h2
      have h4 : symAct 5 K (Equiv.swap i j) d = d := SM.tor.injective h3
      have h5 := congrFun (congrArg Subtype.val h4) i
      rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_left] at h5
      exact h5.symm
  let Zc' : Subgroup ↥T := Zc.subgroupOf T
  let V₀ : Subgroup (torusVec 5 5 K) := Zc'.comap SM.tor.toMonoidHom
  have hV₀le : V₀ ≤ scalarSub 5 5 K := fun d hd => hfwd d hd
  have hV₀card : Nat.card V₀ = 5 := by
    have h1 : Nat.card V₀ = Nat.card (V₀.map SM.tor.toMonoidHom) :=
      (Subgroup.card_map_of_injective SM.tor.injective).symm
    have h2 : V₀.map SM.tor.toMonoidHom = Zc' :=
      Subgroup.map_comap_eq_self_of_surjective SM.tor.surjective _
    have h3 : Nat.card Zc' = Nat.card Zc :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv
    rw [h1, h2, h3, hZcard]
  have hsc : Nat.card (scalarSub 5 5 K) = 5 := card_scalarSub Nat.prime_five (by norm_num)
    (dvd_refl 5) hζ
  have hV₀eq : V₀ = scalarSub 5 5 K := Subgroup.eq_of_le_of_card_ge hV₀le (by rw [hsc, hV₀card])
  constructor
  · exact hfwd d
  · intro hd
    rw [← hV₀eq] at hd
    exact hd

end CFSG.RankThree.PartOne.KFU
