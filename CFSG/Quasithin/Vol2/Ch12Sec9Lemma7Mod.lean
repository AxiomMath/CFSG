module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Sec
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7In

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace L1297

theorem open_pCore_eq (p : ℕ) (A : Type*) [Group A] : CFSG.Open.pCore p A = CFSG.pCore p A :=
  (CFSG.pCore_eq_open A p).symm

theorem comap_pCore_eq_of_isPGroup_ker {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    (CFSG.pCore p B).comap f = CFSG.pCore p A := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := B)).comap f,
      (CFSG.pCore_isPGroup (p := p) (G := B)).comap_of_ker_isPGroup f hk⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := A)).map f hf,
      (CFSG.pCore_isPGroup (p := p) (G := A)).map f⟩

theorem exists_pCore_quotient_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    Nonempty ((A ⧸ CFSG.pCore p A) ≃* (B ⧸ CFSG.pCore p B)) := by
  have hg : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore p B)).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hker : CFSG.pCore p A = ((QuotientGroup.mk' (CFSG.pCore p B)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pCore_eq_of_isPGroup_ker f hf hk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hg)⟩

variable {G : Type} [Group G] [Finite G]

theorem card_conjClosure_eq (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hB : AsB4_12_two) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ H Y : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hV₁₂ : V₁ ≤ V₂) (hHz : IsHzOne T L V₁ H) (hYH : Y ≤ H)
    (hY : H ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Y) (hY₂ : Y ≤ Subgroup.normalizer (V₂ : Set G))
    (hYiso : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hHiso : Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :
    Nat.card ↥(conjClosure V H) = 2 ^ 5 := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  have hidx : (V₁.subgroupOf V₂).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card V₁ V₂
    rw [inf_eq_left.2 hV₁₂, hV₁2, hV₂4] at h1
    have h2 : V₁.relIndex V₂ = 2 := by omega
    exact h2
  obtain ⟨v₂, hv₂, hv₂V₁⟩ : ∃ v₂ ∈ V₂, v₂ ∉ V₁ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from fun x hx => hall x hx)
    rw [hV₁2, hV₂4] at h1
    norm_num at h1
  have hv₂V := hV₂.1 hv₂
  have hA := lemma12_8_4_one h1222 h hV₁ hHz
  have hQ := lemma12_8_4_four h1222 h37 h38 h39 G T L V n h V₁ H hV₁ hHz
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hHz.2.1
  have hHU : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hUN : conjClosure V H ≤ Subgroup.normalizer (V₁ : Set G) := hA.conjClosure_le_N
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hL₁H : lOne L V₁ ≤ H := le_sup_left.trans hHz.1.1
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hL₁V : lOne L V₁ ≤ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans h.hyp.irrPlus.2.2.1
  set U := conjClosure V H with hUdef
  set K := tildeOf V₁ U with hKdef
  set ρ := tRho hHV₁ hHU with hρ
  set v := tElt hUN v₂ (hVU hv₂V) with hvdef
  set G' : Subgroup (MulAut ↥K) := ρ.range with hG'
  have hfix : ∀ x : ↥H, ρ x v = v ↔ (x : G) ∈ Subgroup.normalizer (V₂ : Set G) := by
    intro x
    rw [hρ, hvdef, tRho_tElt_eq_iff hHV₁ hHU hUN x (hVU hv₂V),
      mem_normalizer_iff_commutator_mem hidx hV₁₂ hv₂ hv₂V₁ (hHV₁ x.2)]
  have horbV : ∀ a (ha : a ∈ V), a ∉ V₁ → ∃ x : ↥H, ρ x v = tElt hUN a (hVU ha) := by
    intro a ha haV₁
    obtain ⟨σ, hσ, hσa⟩ := exists_mem_lOne_conj h hV₁ hv₂V ha hv₂V₁ haV₁
    refine ⟨⟨σ, hL₁H hσ⟩, ?_⟩
    rw [hρ, hvdef, tRho_tElt, tElt_eq_iff]
    have hσv : σ * v₂ * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hL₁V hσ) v₂).1 hv₂V
    change (σ * v₂ * σ⁻¹)⁻¹ * a ∈ V₁
    rw [(hab a ha _ (V.inv_mem hσv)).symm]
    have := V₁.inv_mem hσa
    rwa [show (σ * v₂ * σ⁻¹ * a⁻¹)⁻¹ = a * (σ * v₂ * σ⁻¹)⁻¹ by group] at this
  have hker : ρ.ker = CFSG.pCore 2 ↥H := by
    ext x
    rw [MonoidHom.mem_ker, hρ, tRho_eq_one_iff hHV₁ hHU hUN x]
    have e1 : (∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁) ↔
        (x : G) ∈ centralizerMod V₁ H U :=
      ⟨fun h1 => ⟨x.2, hHV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
    rw [e1, hQ]
    change H.subtype x ∈ (CFSG.Open.pCore 2 ↥H).map H.subtype ↔ _
    exact Subgroup.mem_map_iff_mem H.subtype_injective
  have hiso : Nonempty (↥G' ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥G' ≃* alternatingGroup (Fin 7)) := by
    have e : ↥G' ≃* ↥H ⧸ CFSG.pCore 2 ↥H :=
      (QuotientGroup.quotientKerEquivRange ρ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)
    rcases hHiso with he | he
    · obtain ⟨e'⟩ := he
      exact Or.inr ⟨e.trans e'⟩
    · obtain ⟨e'⟩ := he
      exact Or.inl ⟨e.trans e'⟩
  let _ : CommGroup ↥K :=
    { (inferInstance : Group ↥K) with
      mul_comm := fun a b => by
        obtain ⟨u, hu, rfl⟩ := exists_tElt hUN a
        obtain ⟨u', hu', rfl⟩ := exists_tElt hUN b
        rw [tElt_mul, tElt_mul, tElt_eq_iff]
        have := hA.G22_commutator_mem (U.inv_mem hu') (U.inv_mem hu)
        rwa [show u'⁻¹ * u⁻¹ * u'⁻¹⁻¹ * u⁻¹⁻¹ = (u * u')⁻¹ * (u' * u) by group] at this }
  have hexp : ∀ w : ↥K, w ^ 2 = 1 := by
    intro w
    obtain ⟨u, hu, rfl⟩ := exists_tElt hUN w
    rw [sq, tElt_mul, tElt_eq_one_iff]
    have := hA.G22_sq_mem hu
    rwa [sq] at this
  have hmemorb : ∀ w : ↥K, w ∈ orbitOf G' v ↔ ∃ x : ↥H, ρ x v = w := by
    intro w
    constructor
    · rintro ⟨g, ⟨x, rfl⟩, hgw⟩
      exact ⟨x, hgw⟩
    · rintro ⟨x, hx⟩
      exact ⟨ρ x, ⟨x, rfl⟩, hx⟩
  have hgen : Subgroup.closure (orbitOf G' v) = ⊤ := by
    set W := Subgroup.closure (orbitOf G' v) with hW
    have hinv : ∀ x : ↥H, ∀ w ∈ W, ρ x w ∈ W := by
      intro x w hw
      have h1 : W.map (ρ x).toMonoidHom ≤ W := by
        rw [hW, MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨x', hx'⟩ := (hmemorb y).1 hy
        refine (hmemorb _).2 ⟨x * x', ?_⟩
        rw [map_mul, MulAut.mul_apply, hx']
        try rfl
      exact h1 ⟨w, hw, rfl⟩
    let φ : ↥U →* ↥K :=
      ((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp (Subgroup.inclusion hUN)).codRestrict
        K (fun u => secMk_mem_secImg u.2)
    have hφ : ∀ u : ↥U, φ u = tElt hUN u u.2 := fun _ => rfl
    have hP : U ≤ (W.comap φ).map U.subtype := by
      refine conjClosure_le fun x hx a ha => ?_
      have hxa : x * a * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hHU hx) a).1 (hVU ha)
      refine ⟨⟨x * a * x⁻¹, hxa⟩, ?_, rfl⟩
      change φ ⟨x * a * x⁻¹, hxa⟩ ∈ W
      rw [hφ]
      have h1 : tElt hUN (x * a * x⁻¹) hxa = ρ ⟨x, hx⟩ (tElt hUN a (hVU ha)) := by
        rw [hρ, tRho_tElt]
      rw [h1]
      refine hinv ⟨x, hx⟩ _ ?_
      by_cases haV₁ : a ∈ V₁
      · rw [(tElt_eq_one_iff hUN (hVU ha)).2 haV₁]
        exact W.one_mem
      · obtain ⟨y, hy⟩ := horbV a ha haV₁
        rw [← hy]
        exact Subgroup.subset_closure ((hmemorb _).2 ⟨y, rfl⟩)
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu, rfl⟩ := exists_tElt hUN w
    obtain ⟨u', hu'W, hu'⟩ := hP hu
    have : tElt hUN u hu = φ u' := by
      rw [hφ]
      congr 1
      exact hu'.symm
    rw [this]
    exact hu'W
  set U' : Subgroup ↥K := (tildeOf V₁ V).subgroupOf K with hU'
  have hU'orb : ∀ w ∈ U', w ≠ 1 → w ∈ orbitOf G' v := by
    intro w hw hw1
    obtain ⟨a, ha, haw⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hw)
    have hw' : w = tElt hUN a (hVU ha) := Subtype.ext haw.symm
    have haV₁ : (a : G) ∉ V₁ := fun h1 => hw1 (by rw [hw']; exact (tElt_eq_one_iff _ _).2 h1)
    obtain ⟨y, hy⟩ := horbV a ha haV₁
    rw [hw']
    exact (hmemorb _).2 ⟨y, hy⟩
  have hU'2 : ∃ x ∈ U', ∃ y ∈ U', x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
    obtain ⟨u, hu, huV₂⟩ : ∃ u ∈ V, u ∉ V₂ := by
      by_contra hall
      push Not at hall
      have h1 := Subgroup.card_le_of_le (show V ≤ V₂ from fun x hx => hall x hx)
      rw [hcard, hV₂4] at h1
      have hn : 3 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> norm_num
      have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    refine ⟨v, Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hv₂V), tElt hUN u (hVU hu),
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hu), ?_, ?_, ?_⟩
    · exact fun h1 => hv₂V₁ ((tElt_eq_one_iff _ _).1 h1)
    · exact fun h1 => huV₂ (hV₁₂ ((tElt_eq_one_iff _ _).1 h1))
    · intro h1
      have h2 := (tElt_eq_iff _ _ _).1 h1
      apply huV₂
      have := V₂.mul_mem hv₂ (hV₁₂ h2)
      rwa [mul_inv_cancel_left] at this
  have hodd : Odd (Nat.card (orbitOf G' v)) := by
    let _ : MulAction ↥H ↥K := MulAction.compHom _ ρ
    have horb : orbitOf G' v = MulAction.orbit ↥H v := by
      ext w
      rw [hmemorb, MulAction.mem_orbit_iff]
      try rfl
    rw [horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    have hTS : T.subgroupOf H ≤ MulAction.stabilizer ↥H v := by
      intro x hx
      rw [MulAction.mem_stabilizer_iff]
      exact (hfix x).2 (hV₂.2.2 (Subgroup.mem_subgroupOf.1 hx))
    have hT : ¬ 2 ∣ (T.subgroupOf H).index :=
      (isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow hTH).2.2
    have h1 := Subgroup.index_dvd_of_le hTS
    have h2 : ¬ 2 ∣ (MulAction.stabilizer ↥H v).index := fun h2 => hT (h2.trans h1)
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  have hstab : Nonempty (↥(G' ⊓ MulAction.stabilizer (MulAut ↥K) v) ⧸
      CFSG.pCore 2 ↥(G' ⊓ MulAction.stabilizer (MulAut ↥K) v) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    let f : ↥Y →* ↥(G' ⊓ MulAction.stabilizer (MulAut ↥K) v) :=
      (ρ.comp (Subgroup.inclusion hYH)).codRestrict _ (fun y =>
        ⟨⟨Subgroup.inclusion hYH y, rfl⟩, (hfix _).2 (hY₂ y.2)⟩)
    have hf : Function.Surjective f := by
      rintro ⟨g, ⟨x, rfl⟩, hgv⟩
      have hxY : (x : G) ∈ Y := hY ⟨x.2, (hfix x).1 hgv⟩
      exact ⟨⟨x, hxY⟩, rfl⟩
    have hk : IsPGroup 2 f.ker := by
      intro y
      have hy1 : ρ (Subgroup.inclusion hYH y) = 1 := by
        have := y.2
        rw [MonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      have hyQ : Subgroup.inclusion hYH y ∈ CFSG.pCore 2 ↥H := by
        rw [← hker]
        exact hy1
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hyQ⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z => ((z : ↥H) : G)) (congrArg Subtype.val hk)
      simpa using this
    obtain ⟨e⟩ := exists_pCore_quotient_mulEquiv f hf hk
    obtain ⟨e'⟩ := hYiso
    exact ⟨e.symm.trans e'⟩
  have hK4 := (hB ↥K hexp G' v hgen ⟨U', hU'2, hU'orb⟩ hiso hodd hstab).1
  have h1 := card_tildeOf_mul (hV₁.1.trans hVU) hUN
  rw [← hKdef, hK4, hV₁2] at h1
  rw [← h1]
  norm_num

end L1297

end CFSG.Quasithin.H13
