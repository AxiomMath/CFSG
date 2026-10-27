module

public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

theorem exists_hom_of_surjective {V Q H : Type*} [CommGroup V] [CommGroup Q] [Group H]
    (f : V →* Q) (hf : Function.Surjective f) (ρ : H →* MulAut V)
    (hρ : ∀ g v, f v = 1 → f (ρ g v) = 1) :
    ∃ σ : H →* MulAut Q, ∀ g v, σ g (f v) = f (ρ g v) := by
  classical
  have hwd : ∀ g : H, ∀ v w, f v = f w → f (ρ g v) = f (ρ g w) := by
    intro g v w hvw
    have h1 : f (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
    have h2 := hρ g _ h1
    rw [map_mul, map_inv, map_mul, map_inv] at h2
    exact mul_inv_eq_one.1 h2
  obtain ⟨τ, hτ⟩ : ∃ τ : H → Q → Q, ∀ g v, τ g (f v) = f (ρ g v) :=
    ⟨fun g q => f (ρ g (Function.surjInv hf q)), fun g v =>
      hwd g _ _ (Function.surjInv_eq hf (f v))⟩
  have hτmul : ∀ g q q', τ g (q * q') = τ g q * τ g q' := by
    intro g q q'
    obtain ⟨v, rfl⟩ := hf q
    obtain ⟨v', rfl⟩ := hf q'
    rw [← map_mul, hτ, hτ, hτ, map_mul, map_mul]
  have hτcomp : ∀ g g' q, τ (g * g') q = τ g (τ g' q) := by
    intro g g' q
    obtain ⟨v, rfl⟩ := hf q
    rw [hτ g' v, hτ g (ρ g' v), hτ, map_mul, MulAut.mul_apply]
  have hτone : ∀ q, τ 1 q = q := by
    intro q
    obtain ⟨v, rfl⟩ := hf q
    rw [hτ, map_one, MulAut.one_apply]
  let σ₀ : H → MulAut Q := fun g =>
    { toFun := τ g
      invFun := τ g⁻¹
      left_inv := fun q => by rw [← hτcomp, inv_mul_cancel, hτone]
      right_inv := fun q => by rw [← hτcomp, mul_inv_cancel, hτone]
      map_mul' := hτmul g }
  refine ⟨{ toFun := σ₀, map_one' := ?_, map_mul' := ?_ }, fun g v => hτ g v⟩
  · ext q
    exact hτone q
  · intro g g'
    ext q
    exact hτcomp g g' q

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

noncomputable abbrev convM (h : PUHyp M T L) :
    ↥M →* MulAut (IntMod (Uq M T L) h.isElemAbelian_Uq) :=
  convHom h.isElemAbelian_Uq M (le_normalizer_Uq h.le_normalizer)

theorem convM_apply_val (h : PUHyp M T L) (m : ↥M) (v : IntMod (Uq M T L) h.isElemAbelian_Uq) :
    (convM h m v).val = (m : G) * v.val * (m : G)⁻¹ := by
  rw [convM, convHom_apply, convI_apply_val]

structure G2Rep (h : PUHyp M T L) (f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ)
    (φ : ↥M →* ↥(quasithinG2 (ZMod 2))) : Prop where
  surj : Function.Surjective f
  ker : ∀ v, f v = 1 ↔ v.val ∈ Zq M L
  equiv : ∀ m v, f (convM h m v) = g2QAct (ZMod 2) (φ m) (f v)
  L_le : ∀ l : ↥M, (l : G) ∈ L → φ l ∈ g2Derived (ZMod 2)
  L_onto : ∀ δ ∈ g2Derived (ZMod 2), ∃ l : ↥M, (l : G) ∈ L ∧ φ l = δ

theorem PUHyp.exists_g2Rep
    (h : PUHyp M T L)
    (hX : G2NaturalDerived (autI h.isElemAbelian_Uq L) ⊤
      (intSub h.isElemAbelian_Uq (Uq M T L ⊓ Zq M L)) 1) :
    ∃ f φ, G2Rep h f φ := by
  set hU := h.isElemAbelian_Uq
  obtain ⟨K, _, _, hK, hR⟩ := hX
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have := charP_two_of_natCard_two hK2
  obtain ⟨π, β, hβ⟩ := (H.Mathieu.realizes_iff _ _ ⊤ _).1 hR
  let f₀ : IntMod (Uq M T L) hU →* (FFModel.zornQ (quasithinG2 K)).Mod :=
    β.comp (Subgroup.topEquiv.symm : IntMod (Uq M T L) hU ≃* ↥(⊤ : Subgroup _)).toMonoidHom
  let f : IntMod (Uq M T L) hU →* ModQ := (modQEquivK hK2).symm.toMonoidHom.comp f₀
  have hf₀ : ∀ v, f₀ v = β ⟨v, Subgroup.mem_top v⟩ := fun v => rfl
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨u, hu⟩ := hβ.2.2.2.2.2.2.2.1 (modQEquivK hK2 q)
    refine ⟨u.1, ?_⟩
    change (modQEquivK hK2).symm (β ⟨u.1, Subgroup.mem_top u.1⟩) = q
    rw [show (⟨u.1, Subgroup.mem_top u.1⟩ : ↥(⊤ : Subgroup (IntMod (Uq M T L) hU))) = u from rfl,
      hu, MulEquiv.symm_apply_apply]
  have hfker : ∀ v, f v = 1 ↔ v.val ∈ Zq M L := by
    intro v
    change (modQEquivK hK2).symm (f₀ v) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    refine Iff.trans (hβ.2.2.2.2.2.2.2.2.1 ⟨v, Subgroup.mem_top v⟩) ?_
    change v ∈ intSub hU (Uq M T L ⊓ Zq M L) ↔ _
    rw [intSub, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h' => h'.2, fun h' => ⟨v.val_mem, h'⟩⟩
  have hπeq : ∀ (γ : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam) (v : IntMod (Uq M T L) hU),
      f ((π γ : MulAut (IntMod (Uq M T L) hU)) v) =
        g2QAct (ZMod 2) (conjF2Hom hK2 ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (f v) := by
    intro γ v
    have h0 : f₀ ((π γ : MulAut (IntMod (Uq M T L) hU)) v) =
        g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ (f₀ v) := by
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
      have hm' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ (m : Multiplicative _) ∈
          (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
        zornAct_mem_O0 _ (Subgroup.commutator_le_self _) γ m.2
      have h1 := hβ.2.2.2.2.2.2.2.2.2 γ ⟨v, Subgroup.mem_top v⟩ m trivial hm' hm.symm
      change β ⟨(π γ : MulAut _) v, trivial⟩ = g2QAct K ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
        (β ⟨v, Subgroup.mem_top v⟩)
      rw [← hm]
      exact h1
    change (modQEquivK hK2).symm (f₀ ((π γ : MulAut _) v)) = _
    rw [h0]
    have key := congr_modQEquivK_symm hK2 ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩
    rw [show conjF2Hom hK2 ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ =
      ⟨conjF2 hK2 γ.1, conjF2_mem hK2 (Subgroup.commutator_le_self _ γ.2)⟩ from rfl, ← key]
    show _ = (modQEquivK hK2).symm (g2QAct K _
      ((modQEquivK hK2).symm.symm ((modQEquivK hK2).symm (f₀ v))))
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ := exists_hom_of_surjective f hfs (convM h) (fun m v hv => by
    rw [hfker] at hv ⊢
    rw [convM_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Zq h.le_normalizer m.2) _).mp hv)
  have hσext : ∀ m (g : ↥(quasithinG2 (ZMod 2))),
      (∀ v, f (convM h m v) = g2QAct (ZMod 2) g (f v)) → σ m = g2QAct (ZMod 2) g := by
    intro m g hg
    ext q
    obtain ⟨v, rfl⟩ := hfs q
    rw [hσ, hg]
  have hσL : ∀ l : ↥M, (l : G) ∈ L → ∃ δ ∈ g2Derived (ZMod 2), σ l = g2QAct (ZMod 2) δ := by
    intro l hl
    have hmem : convM h l ∈ autI hU L :=
      (mem_autI hU).2 ⟨⟨l, le_normalizer_Uq h.le_normalizer l.2⟩, hl, rfl⟩
    obtain ⟨γ, hγ⟩ := hβ.1 ⟨convM h l, hmem⟩
    refine ⟨conjF2Hom hK2 ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩, ?_, hσext l _ fun v => ?_⟩
    · rw [← map_g2Derived_conjF2Hom hK2]
      exact ⟨_, Subgroup.mem_subgroupOf.2 γ.2, rfl⟩
    · rw [← hπeq γ v, hγ]
  have hLσ : ∀ δ ∈ g2Derived (ZMod 2), ∃ l : ↥M, (l : G) ∈ L ∧ σ l = g2QAct (ZMod 2) δ := by
    intro δ hδ
    rw [← map_g2Derived_conjF2Hom hK2] at hδ
    obtain ⟨g, hg, rfl⟩ := hδ
    let γ : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam :=
      ⟨g.1, Subgroup.mem_subgroupOf.1 hg⟩
    obtain ⟨n, hnL, hn⟩ := (mem_autI hU).1 (π γ).2
    refine ⟨⟨n, h.L_le hnL⟩, hnL, hσext _ _ fun v => ?_⟩
    have e : convM h ⟨n, h.L_le hnL⟩ = (π γ : MulAut (IntMod (Uq M T L) hU)) := by
      rw [← hn]
      rfl
    rw [e, hπeq γ v]
  have hrange : ∀ m, σ m ∈ (g2QAct (ZMod 2)).range := by
    intro m
    have hmL : ∀ l : ↥M, (l : G) ∈ L → ((m * l * m⁻¹ : ↥M) : G) ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.mp (h.le_normalizer m.2) l).mp hl
    have hmL' : ∀ l : ↥M, ((m * l * m⁻¹ : ↥M) : G) ∈ L → (l : G) ∈ L := by
      intro l hl
      have e : l = m⁻¹ * (m * l * m⁻¹) * m⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer (M.inv_mem m.2)) _).mp hl
    refine normalizer_two_Q (σ m) fun x => ?_
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨l, hl, hlδ⟩ := hLσ δ hδ
      obtain ⟨δ', hδ', hδ'e⟩ := hσL _ (hmL l hl)
      refine ⟨δ', hδ', ?_⟩
      rw [← hδ'e, ← hlδ, map_mul, map_mul, map_inv]
    · rintro ⟨δ, hδ, hδe⟩
      obtain ⟨l, hl, hlδ⟩ := hLσ δ hδ
      obtain ⟨δ', hδ', hδ'e⟩ := hσL (m⁻¹ * l * m⁻¹⁻¹)
        (hmL' _ (by rwa [show m * (m⁻¹ * l * m⁻¹⁻¹) * m⁻¹ = l by group]))
      refine ⟨δ', hδ', ?_⟩
      rw [← hδ'e, map_mul, map_mul, map_inv, inv_inv, hlδ, hδe]
      group
  let φ : ↥M →* ↥(quasithinG2 (ZMod 2)) :=
    ((MonoidHom.ofInjective g2QAct_injective).symm.toMonoidHom).comp (σ.codRestrict _ hrange)
  have hφ : ∀ m, g2QAct (ZMod 2) (φ m) = σ m := fun m =>
    MonoidHom.apply_ofInjective_symm g2QAct_injective ⟨σ m, hrange m⟩
  refine ⟨f, φ, hfs, hfker, fun m v => by rw [hφ, hσ], fun l hl => ?_, fun δ hδ => ?_⟩
  · obtain ⟨δ, hδ, hδe⟩ := hσL l hl
    rw [show φ l = δ from g2QAct_injective (by rw [hφ, hδe])]
    exact hδ
  · obtain ⟨l, hl, hle⟩ := hLσ δ hδ
    exact ⟨l, hl, g2QAct_injective (by rw [hφ, hle])⟩

theorem pCoreOf_le_centralizer_Uq' (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  exact h.Uq_le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right)

omit [Finite G] in
theorem isPGroup_map_subgroupOf {X : Type*} [Group X] (φ : ↥M →* X) {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) : IsPGroup 2 ↥((P.subgroupOf M).map φ) :=
  (hP.comap_of_injective M.subtype M.subtype_injective).map φ

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem eq_one_iff (hR : G2Rep h f φ) (m : ↥M) :
    φ m = 1 ↔ ∀ u ∈ Uq M T L, ⁅u, (m : G)⁆ ∈ Zq M L := by
  constructor
  · intro hm u hu
    set v : IntMod (Uq M T L) h.isElemAbelian_Uq := IntMod.mk _ ⟨u, hu⟩ with hv
    have h1 := hR.equiv m v
    rw [hm, map_one, MulAut.one_apply] at h1
    have h2 : f (v * (convM h m v)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [hR.ker] at h2
    have e : (v * (convM h m v)⁻¹).val = ⁅u, (m : G)⁆ := by
      rw [IntMod.val_mul, IntMod.val_inv, convM_apply_val, commutatorElement_def]
      simp [hv, IntMod.mk, IntMod.val, mul_assoc]
    rwa [e] at h2
  · intro hm
    apply g2QAct_injective
    ext q
    obtain ⟨v, rfl⟩ := hR.surj q
    rw [← hR.equiv, map_one, MulAut.one_apply]
    have h2 : f (v * (convM h m v)⁻¹) = 1 := by
      rw [hR.ker]
      have e : (v * (convM h m v)⁻¹).val = ⁅v.val, (m : G)⁆ := by
        rw [IntMod.val_mul, IntMod.val_inv, convM_apply_val, commutatorElement_def]
        group
      rw [e]
      exact hm _ v.val_mem
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2.symm

theorem map_pCoreOf (hR : G2Rep h f φ) {m : ↥M} (hm : (m : G) ∈ pCoreOf 2 M) : φ m = 1 := by
  refine (hR.eq_one_iff m).2 fun u hu => ?_
  have hc := Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer_Uq' h hm) u hu
  have e : ⁅u, (m : G)⁆ = 1 := by rw [commutatorElement_def, hc]; group
  rw [e]
  exact (Zq M L).one_mem

theorem mem_pCoreOf (hR : G2Rep h f φ) {m : ↥M} (hm2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1)
    (hm : φ m = 1) : (m : G) ∈ pCoreOf 2 M :=
  h.mem_pCoreOf_of_comm_Uq_two m.2 hm2 fun u hu => ((hR.eq_one_iff m).1 hm u hu).2

theorem eq_one_iff_mem_pCoreOf (hR : G2Rep h f φ) {m : ↥M} (hmT : (m : G) ∈ T) :
    φ m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
  refine ⟨fun hm => hR.mem_pCoreOf ?_ hm, hR.map_pCoreOf⟩
  obtain ⟨e, he⟩ := h.isPGroup ⟨m, hmT⟩
  exact ⟨e, by simpa using congrArg Subtype.val he⟩

end G2Rep

end CFSG.Quasithin.MS93.S38G
