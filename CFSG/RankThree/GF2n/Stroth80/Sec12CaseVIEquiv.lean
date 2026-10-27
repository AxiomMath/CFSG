module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualSL
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section LgenCentralizer

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Lgen_le_H0 (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  unfold Lgen
  refine iSup₂_le fun m hm x hx => ?_
  have hy : m⁻¹ * x * m ∈ H0 M Z := hc.LB_le_H0 (mem_conjSubgroup.mp hx)
  obtain ⟨hyM, hyC⟩ := hy
  have hxM : x ∈ M := by
    have h := M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)
    have hxe : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [hxe] at h
  refine ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzm : m⁻¹ * z * m ∈ Z := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hm)) z).mp hz
    rwa [inv_inv] at h
  have hcomm := Subgroup.mem_centralizer_iff.mp hyC (m⁻¹ * z * m) hzm
  calc z * x = m * ((m⁻¹ * z * m) * (m⁻¹ * x * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * x * m) * (m⁻¹ * z * m)) * m⁻¹ := by rw [hcomm]
    _ = x * z := by group

end LgenCentralizer

theorem exists_secEquiv_img {G : Type} [Group G] {Q Z V : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    [(Z.subgroupOf V).Normal] {ι F : Type} [Fintype ι] [Field F]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → F)) :
    ∃ Ψ : ↥(M₀.img V) ≃+ (ι → F), ∀ (v : G) (hv : v ∈ V),
      Ψ ⟨M₀.π v, M₀.pi_mem_img hv (hVQ hv)⟩ =
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hv⟩)) := by
  have hπV : ∀ v : ↥V, M₀.π v ∈ M₀.img V := fun v => M₀.pi_mem_img v.2 (hVQ v.2)
  let κ : ↥V →* Multiplicative ↥(M₀.img V) :=
    { toFun := fun v => Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext M₀.pi_one
      map_mul' := fun x y => by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2)) }
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, -, hx⟩ := a.toAdd.2
    exact ⟨⟨x, hxV⟩, by
      show Multiplicative.ofAdd (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥(M₀.img V)) = a
      apply congrArg Multiplicative.ofAdd
      exact Subtype.ext hx⟩
  have hker : κ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2)]
    constructor
    · intro h
      exact congrArg Subtype.val (Multiplicative.ofAdd.injective h)
    · intro h
      exact congrArg Multiplicative.ofAdd (Subtype.ext h)
  let e₁ : ↥V ⧸ κ.ker ≃* Multiplicative ↥(M₀.img V) :=
    QuotientGroup.quotientKerEquivOfSurjective κ hκsurj
  let e₂ : ↥V ⧸ Z.subgroupOf V ≃* ↥V ⧸ κ.ker := QuotientGroup.quotientMulEquivOfEq hker.symm
  let Ψm : Multiplicative ↥(M₀.img V) ≃* Multiplicative (ι → F) :=
    e₁.symm.trans (e₂.symm.trans ψ)
  let Ψ : ↥(M₀.img V) ≃+ (ι → F) := AddEquiv.toMultiplicative.symm Ψm
  have hΨ : ∀ v : ↥V, Ψ ⟨M₀.π v, hπV v⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro v
    show Multiplicative.toAdd (Ψm (Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩)) = _
    have h1 : e₁.symm (κ v) = QuotientGroup.mk v := by
      apply e₁.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 : e₂.symm (QuotientGroup.mk v) = QuotientGroup.mk v := rfl
    show Multiplicative.toAdd (ψ (e₂.symm (e₁.symm (κ v)))) = _
    rw [h1, h2]
  exact ⟨Ψ, fun v hv => hΨ ⟨v, hv⟩⟩

theorem exists_addEquiv_prod_of_isCompl {E : Type} [AddCommGroup E] (E₁ E₂ : AddSubgroup E)
    (h : IsCompl E₁ E₂) :
    ∃ e : E ≃+ ↥E₁ × ↥E₂, ∀ (x : E₁) (y : E₂), e ((x : E) + (y : E)) = (x, y) := by
  let f : ↥E₁ × ↥E₂ →+ E := E₁.subtype.coprod E₂.subtype
  have hf : ∀ (x : E₁) (y : E₂), f (x, y) = (x : E) + (y : E) := fun x y => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : E) + (y : E) = 0 := (hf x y).symm.trans hxy
    have hx0 : (x : E) = 0 := by
      have hmem : (x : E) ∈ E₁ ⊓ E₂ := by
        refine ⟨x.2, ?_⟩
        rw [eq_neg_of_add_eq_zero_left hxy']
        exact E₂.neg_mem y.2
      rw [h.inf_eq_bot] at hmem
      exact AddSubgroup.mem_bot.mp hmem
    have hy0 : (y : E) = 0 := by
      rw [hx0, zero_add] at hxy'
      exact hxy'
    exact Prod.ext (Subtype.ext hx0) (Subtype.ext hy0)
  have hsurj : Function.Surjective f := by
    intro e
    have he : e ∈ E₁ ⊔ E₂ := by
      rw [h.sup_eq_top]
      exact AddSubgroup.mem_top e
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp he
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  refine ⟨(AddEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, fun x y => ?_⟩
  exact (AddEquiv.ofBijective f ⟨hinj, hsurj⟩).symm_apply_eq.mpr (hf x y).symm

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

theorem isCompl_img {G : Type} [Group G] {Q Z V₁ V₂ : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (hZV₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q) (hZV₂ : Z ≤ V₂)
    (hV₂Q : V₂ ≤ Q) (hinf : V₁ ⊓ V₂ = Z) (hsup : V₁ ⊔ V₂ = Q) :
    IsCompl (M₀.img V₁) (M₀.img V₂) := by
  have hdisj : Disjoint (M₀.img V₁) (M₀.img V₂) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro e ⟨he₁, he₂⟩
    obtain ⟨x, hxV₁, hxQ, rfl⟩ := he₁
    have hxV₂ : x ∈ V₂ := (M₀.mem_img_iff hZV₂ hxQ).mp he₂
    have hxZ : x ∈ V₁ ⊓ V₂ := ⟨hxV₁, hxV₂⟩
    rw [hinf] at hxZ
    exact AddSubgroup.mem_bot.mpr ((M₀.π_ker x hxQ).mpr hxZ)
  have hcodisj : Codisjoint (M₀.img V₁) (M₀.img V₂) := by
    rw [codisjoint_iff, eq_top_iff]
    intro e _
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    obtain ⟨T, hT⟩ : ∃ T : Subgroup G, ∀ y : G,
        y ∈ T ↔ y ∈ Q ∧ M₀.π y ∈ M₀.img V₁ ⊔ M₀.img V₂ := by
      refine ⟨{ carrier := {y | y ∈ Q ∧ M₀.π y ∈ M₀.img V₁ ⊔ M₀.img V₂}
                mul_mem' := ?_
                one_mem' := ?_
                inv_mem' := ?_ }, fun y => Iff.rfl⟩
      · intro y z hy hz
        refine ⟨Q.mul_mem hy.1 hz.1, ?_⟩
        rw [M₀.π_mul y hy.1 z hz.1]
        exact (M₀.img V₁ ⊔ M₀.img V₂).add_mem hy.2 hz.2
      · refine ⟨Q.one_mem, ?_⟩
        rw [M₀.pi_one]
        exact (M₀.img V₁ ⊔ M₀.img V₂).zero_mem
      · intro y hy
        refine ⟨Q.inv_mem hy.1, ?_⟩
        rw [M₀.pi_inv hy.1]
        exact (M₀.img V₁ ⊔ M₀.img V₂).neg_mem hy.2
    have h1 : V₁ ≤ T := by
      intro y hy
      exact (hT y).mpr ⟨hV₁Q hy, AddSubgroup.mem_sup_left (M₀.pi_mem_img hy (hV₁Q hy))⟩
    have h2 : V₂ ≤ T := by
      intro y hy
      exact (hT y).mpr ⟨hV₂Q hy, AddSubgroup.mem_sup_right (M₀.pi_mem_img hy (hV₂Q hy))⟩
    have hxsup : x ∈ V₁ ⊔ V₂ := by
      rw [hsup]
      exact hxQ
    exact ((hT x).mp (sup_le h1 h2 hxsup)).2
  exact ⟨hdisj, hcodisj⟩

theorem exists_equivariant_coord {G : Type} [Group G] {Q Z V₁ V₂ S : Subgroup G} {K : Type}
    [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {n : ℕ} {F : Type} [Field F]
    (ρ : ↥S →* (M₀.E ≃ₗ[K] M₀.E))
    (hρπ : ∀ (s : ↥S) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = ρ s (M₀.π x))
    (hZV₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q) (hZV₂ : Z ≤ V₂) (hV₂Q : V₂ ≤ Q) (hinf : V₁ ⊓ V₂ = Z)
    (hsup : V₁ ⊔ V₂ = Q) (φ' : ↥S →* GL (Fin n) F)
    (hact₁ : SectionAct (ι := Fin n) F S V₁ Z φ' (fun g => (g : Matrix (Fin n) (Fin n) F)))
    (hact₂ : SectionAct (ι := Fin n) F S V₂ Z φ'
      (fun g => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ)) :
    ∃ Φ : M₀.E ≃+ (Fin n → F) × (Fin n → F),
      (∀ (s : ↥S) (e : M₀.E),
        Φ (ρ s e) = (((φ' s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Φ e).1,
          ((tinvGL (φ' s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Φ e).2)) ∧
      (∀ e : M₀.E, e ∈ M₀.img V₁ ↔ (Φ e).2 = 0) ∧
      (∀ e : M₀.E, e ∈ M₀.img V₂ ↔ (Φ e).1 = 0) := by
  obtain ⟨hSN₁, hN₁, ψ₁, hψ₁⟩ := hact₁
  obtain ⟨hSN₂, hN₂, ψ₂, hψ₂⟩ := hact₂
  haveI := hN₁
  haveI := hN₂
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_secEquiv_img M₀ hV₁Q hZV₁ ψ₁
  obtain ⟨Ψ₂, hΨ₂⟩ := exists_secEquiv_img M₀ hV₂Q hZV₂ ψ₂
  have hcompl : IsCompl (M₀.img V₁) (M₀.img V₂) :=
    isCompl_img M₀ hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup
  obtain ⟨e₀, he₀⟩ := exists_addEquiv_prod_of_isCompl (M₀.img V₁) (M₀.img V₂) hcompl
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M₀.E ≃+ (Fin n → F) × (Fin n → F),
      ∀ (a : ↥(M₀.img V₁)) (b : ↥(M₀.img V₂)),
        Φ ((a : M₀.E) + (b : M₀.E)) = (Ψ₁ a, Ψ₂ b) := by
    refine ⟨e₀.trans (Ψ₁.prodCongr Ψ₂), fun a b => ?_⟩
    rw [AddEquiv.trans_apply, he₀ a b]
    rfl
  have hdec : ∀ e : M₀.E, ∃ (a : ↥(M₀.img V₁)) (b : ↥(M₀.img V₂)),
      e = (a : M₀.E) + (b : M₀.E) := by
    intro e
    have h : e₀ (((e₀ e).1 : M₀.E) + ((e₀ e).2 : M₀.E)) = e₀ e := he₀ (e₀ e).1 (e₀ e).2
    exact ⟨(e₀ e).1, (e₀ e).2, (e₀.injective h).symm⟩
  have hA : ∀ (s : ↥S) (e : M₀.E) (he : e ∈ M₀.img V₁), ∃ hre : ρ s e ∈ M₀.img V₁,
      Ψ₁ ⟨ρ s e, hre⟩ = ((φ' s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ Ψ₁ ⟨e, he⟩ := by
    intro s e he
    obtain ⟨v, hvV₁, hvQ, rfl⟩ := he
    have hw : (s : G) * v * (s : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hSN₁ s.2) v).mp hvV₁
    have hρ : ρ s (M₀.π v) = M₀.π ((s : G) * v * (s : G)⁻¹) := (hρπ s v hvQ).symm
    have hre : ρ s (M₀.π v) ∈ M₀.img V₁ := by
      rw [hρ]
      exact M₀.pi_mem_img hw (hV₁Q hw)
    refine ⟨hre, ?_⟩
    have e1 : Ψ₁ ⟨ρ s (M₀.π v), hre⟩ =
        Ψ₁ ⟨M₀.π ((s : G) * v * (s : G)⁻¹), M₀.pi_mem_img hw (hV₁Q hw)⟩ :=
      congrArg Ψ₁ (Subtype.ext hρ)
    rw [e1, hΨ₁ _ hw, hΨ₁ v hvV₁]
    exact hψ₁ s ⟨v, hvV₁⟩ ⟨(s : G) * v * (s : G)⁻¹, hw⟩ rfl
  have hB : ∀ (s : ↥S) (e : M₀.E) (he : e ∈ M₀.img V₂), ∃ hre : ρ s e ∈ M₀.img V₂,
      Ψ₂ ⟨ρ s e, hre⟩ =
        ((tinvGL (φ' s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ Ψ₂ ⟨e, he⟩ := by
    intro s e he
    obtain ⟨v, hvV₂, hvQ, rfl⟩ := he
    have hw : (s : G) * v * (s : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hSN₂ s.2) v).mp hvV₂
    have hρ : ρ s (M₀.π v) = M₀.π ((s : G) * v * (s : G)⁻¹) := (hρπ s v hvQ).symm
    have hre : ρ s (M₀.π v) ∈ M₀.img V₂ := by
      rw [hρ]
      exact M₀.pi_mem_img hw (hV₂Q hw)
    refine ⟨hre, ?_⟩
    have e1 : Ψ₂ ⟨ρ s (M₀.π v), hre⟩ =
        Ψ₂ ⟨M₀.π ((s : G) * v * (s : G)⁻¹), M₀.pi_mem_img hw (hV₂Q hw)⟩ :=
      congrArg Ψ₂ (Subtype.ext hρ)
    rw [e1, hΨ₂ _ hw, hΨ₂ v hvV₂]
    exact hψ₂ s ⟨v, hvV₂⟩ ⟨(s : G) * v * (s : G)⁻¹, hw⟩ rfl
  have hV₁ : ∀ b : ↥(M₀.img V₂), (b : M₀.E) ∈ M₀.img V₁ ↔ b = 0 := by
    intro b
    constructor
    · intro hb
      have hbot : (b : M₀.E) ∈ M₀.img V₁ ⊓ M₀.img V₂ := ⟨hb, b.2⟩
      rw [hcompl.inf_eq_bot] at hbot
      exact Subtype.ext (AddSubgroup.mem_bot.mp hbot)
    · intro hb
      rw [hb]
      exact (M₀.img V₁).zero_mem
  have hV₂ : ∀ a : ↥(M₀.img V₁), (a : M₀.E) ∈ M₀.img V₂ ↔ a = 0 := by
    intro a
    constructor
    · intro ha
      have hbot : (a : M₀.E) ∈ M₀.img V₂ ⊓ M₀.img V₁ := ⟨ha, a.2⟩
      rw [hcompl.symm.inf_eq_bot] at hbot
      exact Subtype.ext (AddSubgroup.mem_bot.mp hbot)
    · intro ha
      rw [ha]
      exact (M₀.img V₂).zero_mem
  refine ⟨Φ, fun s e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hdec e
    obtain ⟨hra, hra'⟩ := hA s (a : M₀.E) a.2
    obtain ⟨hrb, hrb'⟩ := hB s (b : M₀.E) b.2
    have hsum : ρ s ((a : M₀.E) + (b : M₀.E)) =
        ((⟨ρ s (a : M₀.E), hra⟩ : ↥(M₀.img V₁)) : M₀.E) +
          ((⟨ρ s (b : M₀.E), hrb⟩ : ↥(M₀.img V₂)) : M₀.E) :=
      map_add (ρ s) _ _
    rw [hsum, hΦ, hΦ]
    exact Prod.ext hra' hrb'
  · obtain ⟨a, b, rfl⟩ := hdec e
    rw [hΦ a b]
    show _ ↔ Ψ₂ b = 0
    exact ((add_mem_cancel_left a.2).trans (hV₁ b)).trans Ψ₂.map_eq_zero_iff.symm
  · obtain ⟨a, b, rfl⟩ := hdec e
    rw [hΦ a b]
    show _ ↔ Ψ₁ a = 0
    exact ((add_mem_cancel_right b.2).trans (hV₂ a)).trans Ψ₁.map_eq_zero_iff.symm

end CFSG.RankThree.GF2n.Stroth80
