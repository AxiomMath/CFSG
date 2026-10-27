module

public import CFSG.Quasithin.Background.G64NatTop

public section

namespace CFSG.Quasithin

namespace SzG11

open CFSG.Quasithin.G64 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem hyp61_of_hypothesis61 [Finite V] {X : Subgroup (MulAut V)} {a : MulAut V}
    (h : G6.Hypothesis61 X a) : G64.Hyp61 X a where
  pCore_eq_bot := h.pCoreOf_eq_bot
  quotient_sqtk := by
    obtain ⟨S, _, _, hS, φ, hφ⟩ := h.isQuotientOfSQTK
    exact ⟨S, inferInstance, inferInstance, φ.ker, inferInstance, hS,
      ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm⟩⟩
  mem := h.mem
  ne_one := h.ne_one
  sq_eq_one := by rw [pow_two]; exact h.mul_self
  card_comm_le := by simpa using h.card_commV_le
  span := h.span

theorem exists_secHomU {D : FFModel} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) :
    ∃ β : ↥D.sec →* V, β.range = U ∧ (∀ m : ↥D.sec, β m = 1 ↔ (m : D.Amb) ∈ D.ker) ∧
      ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
        β ⟨D.act γ (m : D.Amb), hm⟩ = ((π γ : ↥H) : MulAut V) (β m) := by
  obtain ⟨_, _, _, hHU, _, _, _, β₀, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  let e : ↥U ≃* D.Mod := MulEquiv.ofBijective β₀ ⟨hβi, hβs⟩
  refine ⟨(U.subtype.comp e.symm.toMonoidHom).comp (QuotientGroup.mk' (D.ker.subgroupOf D.sec)),
    ?_, fun m => ?_, fun γ m hm => ?_⟩
  · ext v
    constructor
    · rintro ⟨m, rfl⟩
      exact (e.symm (QuotientGroup.mk m)).2
    · intro hv
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e ⟨v, hv⟩)
      refine ⟨m, ?_⟩
      show ((e.symm (QuotientGroup.mk m) : ↥U) : V) = v
      rw [hm, MulEquiv.symm_apply_apply]
  · show ((e.symm (QuotientGroup.mk m) : ↥U) : V) = 1 ↔ _
    rw [← Subgroup.coe_one U, Subtype.coe_inj, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · show ((e.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩) : ↥U) : V) =
      ((π γ : ↥H) : MulAut V) ((e.symm (QuotientGroup.mk m) : ↥U) : V)
    set u : ↥U := e.symm (QuotientGroup.mk m) with hu
    have hu' : β₀ u = QuotientGroup.mk m := by
      rw [hu]
      exact e.apply_symm_apply _
    have hu2 : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
    have := hβe γ u m hu2 hm hu'
    have h2 : e.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩) = ⟨_, hu2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact this.symm
    rw [h2]

theorem isSymModule_of_realizes {n : ℕ} {Z : Subgroup (G6.PermMod n)}
    (hfaith : (permModel n Z).Faithful) {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : Equiv.Perm (Fin n) →* ↥H} (h : (permModel n Z).RealizesVia H U ⊥ π) :
    ∃ (θ : ↥H ≃* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* V),
      (∀ (x : ↥H) (u : ↥(G6.coreMod n)), β (G6.coreAct n (θ x) u) = (x : MulAut V) (β u)) ∧
        β.range = U ∧ ∀ m : ↥(G6.coreMod n), β m = 1 ↔ (m : G6.PermMod n) ∈ Z := by
  have hinj : Function.Injective π := RealizesVia.injective_of_faithful' hfaith h
  obtain ⟨β, hrange, hker, he⟩ := exists_secHomU h
  refine ⟨(MulEquiv.ofBijective π ⟨hinj, h.1⟩).symm, β, fun x u => ?_, hrange, hker⟩
  have hx : π ((MulEquiv.ofBijective π ⟨hinj, h.1⟩).symm x) = x :=
    (MulEquiv.ofBijective π ⟨hinj, h.1⟩).apply_symm_apply x
  have h2 : ((π ((MulEquiv.ofBijective π ⟨hinj, h.1⟩).symm x) : ↥H) : MulAut V) = (x : MulAut V) :=
    congrArg Subtype.val hx
  rw [← h2]
  exact he _ u (G6.permAct_mem_coreMod _ u.2)

theorem isSymNatural_of_symmetricNatural {n : ℕ} (hn : 5 ≤ n) {H : Subgroup (MulAut V)}
    {U : Subgroup V} (h : SymmetricNatural H U ⊥ n) : G6.IsSymNatural H U n := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨θ, β, he, hr, hk⟩ := isSymModule_of_realizes (Z := Subgroup.zpowers (G6.allOnes n) ⊓
    G6.coreMod n) (symDn_faithful hn) hπ
  refine ⟨θ, β, he, hr, ?_⟩
  ext m
  rw [MonoidHom.mem_ker, hk]
  exact ⟨fun hm => hm.1, fun hm => ⟨hm, m.2⟩⟩

theorem isSymCore_of_symmetricCore {n : ℕ} (hn : 3 ≤ n) {H : Subgroup (MulAut V)}
    {U : Subgroup V} (h : G64.SymmetricCore H U ⊥ n) : G6.IsSymCore H U n := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨θ, β, he, hr, hk⟩ := isSymModule_of_realizes (Z := ⊥) (symCore_faithful hn) hπ
  refine ⟨θ, β, he, hr, ?_⟩
  ext m
  rw [MonoidHom.mem_ker, hk, Subgroup.mem_bot, Subgroup.mem_bot]
  exact ⟨fun hm => Subtype.ext hm, fun hm => congrArg Subtype.val hm⟩

noncomputable def statedSLEquivGL (n : ℕ) :
    ↥(StatedSL n (ZMod 2)) ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  (MulEquiv.subgroupCongr (eq_top_iff.2 fun x _ => mem_statedSL_zmod x)).trans Subgroup.topEquiv

theorem isLnNatural_of_binaryNaturalSL {n : ℕ} {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : BinaryNaturalSL H U ⊥ n 1) : G6.IsLnNatural H U n := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h
  have hinj : Function.Injective π := natSL_injective hπ
  refine ⟨⟨((MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm).trans (statedSLEquivGL n)⟩, ?_, ?_⟩
  · have := RealizesVia.card_eq hπ
    rw [card_natMod, Nat.card_zmod, Subgroup.card_bot] at this
    simpa using this
  · intro x hx hfix
    exact RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) hπ hx
      (fun u hu => by simp [hfix u hu])

theorem isSmallG64Type_of_factorType {H : Subgroup (MulAut V)} (h : G64.FactorType H) :
    G6.IsSmallG64Type H := by
  rcases h with he | he | h5
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨e.trans (statedSLEquivGL 2)⟩
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inl ⟨e.trans (statedSLEquivGL 3)⟩)
  · exact Or.inr (Or.inr h5)

theorem isG64Type_of_moduleType {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : G64.ModuleType H U) : G6.IsG64Type H U := by
  rcases h with ⟨n, h2, h5, hn⟩ | ⟨n, h5, h8, hn⟩ | ⟨n, h68, hn⟩
  · exact Or.inl ⟨n, h2, h5, isLnNatural_of_binaryNaturalSL hn⟩
  · exact Or.inr (Or.inl ⟨n, h5, h8, isSymNatural_of_symmetricNatural h5 hn⟩)
  · exact Or.inr (Or.inr ⟨n, h68, isSymCore_of_symmetricCore (by omega) hn⟩)

end SzG11

end CFSG.Quasithin
