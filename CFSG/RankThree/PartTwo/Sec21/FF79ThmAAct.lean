module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG

variable {G : Type} [Group G]

@[expose] def conjAut (N : Subgroup G) (g : G) (hg : g ∈ Nor N) : MulAut ↥N where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
      (by simpa [mul_assoc] using x.2)
    exact h⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[expose] def conjHom (N : Subgroup G) : ↥(Nor N) →* MulAut ↥N where
  toFun g := conjAut N g g.2
  map_one' := by ext; simp [conjAut]
  map_mul' g h := by ext; simp [conjAut, mul_assoc]

@[expose] noncomputable def pPrimeQuotMulAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ pPrimeCore 3 H) where
  toFun σ := QuotientGroup.congr _ _ σ (pPrimeCore_map_iso 3 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def layerMulAut (Q : Type*) [Group Q] :
    MulAut Q →* MulAut ↥(layer Q) where
  toFun σ := (MulEquiv.subgroupMap σ (layer Q)).trans
    (MulEquiv.subgroupCongr (WholeGroup.layer_map_mulEquiv σ))
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

theorem layerMulAut_coe {Q : Type*} [Group Q] (σ : MulAut Q) (e : ↥(layer Q)) :
    ((layerMulAut Q σ e : ↥(layer Q)) : Q) = σ (e : Q) := rfl

abbrev LayerQ (N : Subgroup G) : Type := ↥(layer (↥N ⧸ pPrimeCore 3 ↥N))

@[expose] noncomputable def actE (N : Subgroup G) : ↥(Nor N) →* MulAut (LayerQ N) :=
  (layerMulAut _).comp ((pPrimeQuotMulAut ↥N).comp (conjHom N))

theorem actE_coe (N : Subgroup G) (g : ↥(Nor N)) (e : LayerQ N) (x : ↥N)
    (hx : (e : ↥N ⧸ pPrimeCore 3 ↥N) = (x : ↥N ⧸ pPrimeCore 3 ↥N)) :
    ((actE N g e : LayerQ N) : ↥N ⧸ pPrimeCore 3 ↥N) =
      ((⟨g * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥N) :
        ↥N ⧸ pPrimeCore 3 ↥N) := by
  show pPrimeQuotMulAut ↥N (conjHom N g) (e : ↥N ⧸ pPrimeCore 3 ↥N) = _
  rw [hx]
  rfl

theorem mem_OppE {N : Subgroup G} {x : G} :
    x ∈ OppE 3 N ↔ ∃ h : x ∈ N, ((⟨x, h⟩ : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N) ∈
      layer (↥N ⧸ pPrimeCore 3 ↥N) := by
  unfold OppE
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem OppE_le (N : Subgroup G) : OppE 3 N ≤ N := fun _ hx => (mem_OppE.mp hx).1

theorem Opp_le_OppE (N : Subgroup G) : Opp 3 N ≤ OppE 3 N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine mem_OppE.mpr ⟨y.2, ?_⟩
  have h1 : ((y : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N) = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  show ((⟨(y : G), y.2⟩ : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N) ∈ _
  have e : (⟨(y : G), y.2⟩ : ↥N) = y := rfl
  rw [e, h1]
  exact Subgroup.one_mem _

@[expose] noncomputable def Lπ (N : Subgroup G) : ↥(OppE 3 N) →* LayerQ N where
  toFun l := ⟨((⟨l, OppE_le N l.2⟩ : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N), (mem_OppE.mp l.2).2⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem Lπ_eq_one_iff (N : Subgroup G) (l : ↥(OppE 3 N)) :
    Lπ N l = 1 ↔ (l : G) ∈ Opp 3 N := by
  have h1 : Lπ N l = 1 ↔ ((⟨l, OppE_le N l.2⟩ : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N) = 1 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [h1, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    have : y = ⟨l, OppE_le N l.2⟩ := Subtype.ext hyx
    rwa [← this]

section Finite

variable [Finite G]

theorem coprime_three_card_opp (N : Subgroup G) : Nat.Coprime 3 (Nat.card (Opp 3 N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Opp inSubgroup
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

noncomputable def kerLπEquiv (N : Subgroup G) : (Lπ N).ker ≃ Opp 3 N where
  toFun l := ⟨(l : ↥(OppE 3 N)), (Lπ_eq_one_iff N l).mp l.2⟩
  invFun x := ⟨⟨x, Opp_le_OppE N x.2⟩, (Lπ_eq_one_iff N _).mpr x.2⟩
  left_inv l := rfl
  right_inv x := rfl

theorem coprime_three_card_ker (N : Subgroup G) : Nat.Coprime 3 (Nat.card (Lπ N).ker) := by
  rw [Nat.card_congr (kerLπEquiv N)]
  exact coprime_three_card_opp N

theorem eq_one_of_mem_opp {N U : Subgroup G} (hU : IsPGroup 3 U) {x : G} (hx : x ∈ U)
    (hxo : x ∈ Opp 3 N) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
  have h1 : orderOf x ∣ 3 ^ k := by
    have : orderOf (⟨x, hx⟩ : U) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf x ∣ Nat.card (Opp 3 N) := by
    have : orderOf (⟨x, hxo⟩ : Opp 3 N) ∣ Nat.card (Opp 3 N) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (3 ^ k) (Nat.card (Opp 3 N)) := (coprime_three_card_opp N).pow_left k
  have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.mp this

@[expose] noncomputable def Uπ {N U : Subgroup G} (hUL : U ≤ OppE 3 N) : ↥U →* LayerQ N :=
  (Lπ N).comp (Subgroup.inclusion hUL)

theorem Uπ_injective_of {N W : Subgroup G} (hWL : W ≤ OppE 3 N)
    (h : ∀ x ∈ W, x ∈ Opp 3 N → x = 1) : Function.Injective (Uπ hWL) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : Lπ N (Subgroup.inclusion hWL u) = 1 := hu
  have h2 := (Lπ_eq_one_iff N _).mp h1
  exact Subtype.ext (h u u.2 h2)

theorem Uπ_injective {N U : Subgroup G} (hU : IsPGroup 3 U) (hUL : U ≤ OppE 3 N) :
    Function.Injective (Uπ hUL) :=
  Uπ_injective_of hUL fun _ hx hxo => eq_one_of_mem_opp hU hx hxo

theorem card_range_Uπ {N U : Subgroup G} (hU : IsPGroup 3 U) (hUL : U ≤ OppE 3 N) :
    Nat.card (Uπ hUL).range = Nat.card U :=
  (Nat.card_congr (MonoidHom.ofInjective (Uπ_injective hU hUL)).toEquiv).symm

end Finite

theorem Lπ_surjective (N : Subgroup G) : Function.Surjective (Lπ N) := by
  intro e
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e : ↥N ⧸ pPrimeCore 3 ↥N)
  have hmem : (y : G) ∈ OppE 3 N := mem_OppE.mpr ⟨y.2, by
    have := e.2
    rw [← hy] at this
    exact this⟩
  exact ⟨⟨y, hmem⟩, Subtype.ext hy⟩

theorem actE_Lπ (N : Subgroup G) (g : ↥(Nor N)) (l l' : ↥(OppE 3 N))
    (h : (l' : G) = g * l * (g : G)⁻¹) : actE N g (Lπ N l) = Lπ N l' := by
  apply Subtype.ext
  rw [actE_coe N g (Lπ N l) ⟨l, OppE_le N l.2⟩ rfl]
  have : (⟨(g : G) * (l : G) * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 l).mp
    (OppE_le N l.2)⟩ : ↥N) = ⟨l', OppE_le N l'.2⟩ := Subtype.ext h.symm
  rw [this]
  rfl

end CFSG.RankThree.PartTwo.Sec21.FF79
