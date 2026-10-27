module

public import CFSG.Quasithin.Vol2.Ch3zTrans
public import CFSG.Quasithin.Vol2.Ch3wLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 RegularWreathProduct CFSG.Quasithin.Ch3z
open scoped commutatorElement

namespace Ch3w

section PreImage

variable {G : Type} [Group G] {H L N U : Subgroup G}

theorem chief_nl (hstep : IsChiefStep H U L N) (hUH : U ≤ H) :
    N ≤ Subgroup.normalizer (L : Set G) :=
  (hstep.1.1.trans hUH).trans (Setting.hHL hstep)

@[expose] noncomputable def preHom (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (W : Subgroup ↥(chiefMod L N)) : ↥(chiefPre hNL W) →* ↥W :=
  ((chiefIota hNL).comp (Subgroup.inclusion (chiefPre_le hNL W))).codRestrict W
    (fun x => ((mem_chiefPre hNL W).1 x.2).2)

theorem preHom_surjective (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (W : Subgroup ↥(chiefMod L N)) : Function.Surjective (preHom hNL W) := by
  rintro ⟨w, hw⟩
  obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
  exact ⟨⟨(n : G), (mem_chiefPre hNL W).2 ⟨n.2, hw⟩⟩, Subtype.ext rfl⟩

theorem preHom_ker (hNL : N ≤ Subgroup.normalizer (L : Set G)) (W : Subgroup ↥(chiefMod L N)) :
    (preHom hNL W).ker = L.subgroupOf (chiefPre hNL W) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : chiefIota hNL (Subgroup.inclusion (chiefPre_le hNL W) x) = 1 :=
      congrArg Subtype.val h
    exact (chiefIota_eq_one_iff hNL _).1 h1
  · intro h
    apply Subtype.ext
    exact (chiefIota_eq_one_iff hNL (Subgroup.inclusion (chiefPre_le hNL W) x)).2 h

@[expose] noncomputable def preQuotEquiv (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (W : Subgroup ↥(chiefMod L N)) [(L.subgroupOf (chiefPre hNL W)).Normal] :
    ↥(chiefPre hNL W) ⧸ L.subgroupOf (chiefPre hNL W) ≃* ↥W :=
  (QuotientGroup.quotientMulEquivOfEq (preHom_ker hNL W).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (preHom hNL W) (preHom_surjective hNL W))

theorem preQuotEquiv_mk (hNL : N ≤ Subgroup.normalizer (L : Set G)) (W : Subgroup ↥(chiefMod L N))
    [(L.subgroupOf (chiefPre hNL W)).Normal] (x : ↥(chiefPre hNL W)) :
    preQuotEquiv hNL W (QuotientGroup.mk x) = preHom hNL W x := rfl

end PreImage

section Block

variable {G : Type} [Group G] {H L N U : Subgroup G}

@[expose] noncomputable def blockPre (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (Hj : Subgroup (MulAut ↥(chiefMod L N))) :
    Subgroup G :=
  (Hj.comap (chiefPsi hHL hHN)).map H.subtype

theorem mem_blockPre (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (Hj : Subgroup (MulAut ↥(chiefMod L N))) {g : G} :
    g ∈ blockPre hHL hHN Hj ↔ ∃ hg : g ∈ H, chiefPsi hHL hHN ⟨g, hg⟩ ∈ Hj := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem blockPre_le (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (Hj : Subgroup (MulAut ↥(chiefMod L N))) :
    blockPre hHL hHN Hj ≤ H := fun _ hg => ((mem_blockPre hHL hHN Hj).1 hg).1

theorem sym_faithful_of_data {V : Type} [CommGroup V] {m : ℕ} (hm : Odd m) {Hj : Subgroup (MulAut V)}
    (θ : ↥Hj ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* V)
    (heq : ∀ (x : ↥Hj) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u))
    (hrange : β.range = commV Hj) (hker : β.ker = ⊥) {a : MulAut V} (ha : a ∈ Hj)
    (hfix : ∀ w ∈ commV Hj, a w = w) : a = 1 := by
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : u ∈ β.ker := hu
    rw [hker] at this
    simpa using this
  have h1 : coreAct m (θ ⟨a, ha⟩) = 1 := by
    refine MulEquiv.ext fun w => hβinj ?_
    rw [heq]
    show a (β w) = β w
    exact hfix _ (hrange ▸ ⟨w, rfl⟩)
  have h2 : θ ⟨a, ha⟩ = 1 := (coreAct_eq_one_iff m hm _).mp h1
  have h3 : (⟨a, ha⟩ : ↥Hj) = 1 := θ.injective (h2.trans (map_one θ).symm)
  exact congrArg Subtype.val h3

theorem comm_mem_of_chiefPsi_fix (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (g : ↥H) {n : G} (hn : n ∈ N)
    (h : chiefPsi hHL hHN g (chiefIota hNL ⟨n, hn⟩) = chiefIota hNL ⟨n, hn⟩) :
    (g : G) * n * (g : G)⁻¹ * n⁻¹ ∈ L := by
  have hgn : (g : G) * n * (g : G)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN g.2) n).mp hn
  rw [chiefPsi_iota hHL hHN hNL g ⟨n, hn⟩ hgn] at h
  have h1 : chiefIota hNL (⟨(g : G) * n * (g : G)⁻¹, hgn⟩ * ⟨n, hn⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact (chiefIota_eq_one_iff hNL _).1 h1

theorem naturalSn_block (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (chiefMod L N)) {m : ℕ} (hm : Odd m)
    {Hj : Subgroup (MulAut ↥(chiefMod L N))} (hHj : Hj ≤ chiefAut H L N)
    (θ : ↥Hj ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* ↥(chiefMod L N))
    (heq : ∀ (x : ↥Hj) (u : ↥(coreMod m)),
      β (coreAct m (θ x) u) = (x : MulAut ↥(chiefMod L N)) (β u))
    (hrange : β.range = @commV _ (chiefCG hE) Hj) (hker : β.ker = ⊥)
    [(L.subgroupOf (chiefPre (chief_nl hstep hUH) (@commV _ (chiefCG hE) Hj))).Normal] :
    NaturalSn m (blockPre (Setting.hHL hstep) (Setting.hHN hstep) Hj) L
      (chiefPre (chief_nl hstep hUH) (@commV _ (chiefCG hE) Hj)) := by
  classical
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := chief_nl hstep hUH
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  set W : Subgroup ↥(chiefMod L N) := commV Hj with hW
  set Xj : Subgroup G := chiefPre hNL W with hXj
  set Fj : Subgroup G := blockPre hHL hHN Hj with hFj
  have hfaith : ∀ a ∈ Hj, (∀ w ∈ W, a w = w) → a = 1 := fun a ha hfix =>
    sym_faithful_of_data hm θ β heq hrange hker ha hfix
  let e : ↥(Hj.comap (chiefPsi hHL hHN)) ≃* ↥Fj :=
    Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective
  let ψHj : ↥(Hj.comap (chiefPsi hHL hHN)) →* ↥Hj :=
    ((chiefPsi hHL hHN).comp (Hj.comap (chiefPsi hHL hHN)).subtype).codRestrict Hj (fun x => x.2)
  let θ' : ↥Fj →* Equiv.Perm (Fin m) := (θ.toMonoidHom.comp ψHj).comp e.symm.toMonoidHom
  have hβW : ∀ u, β u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  let β' : ↥(coreMod m) →* ↥Xj ⧸ L.subgroupOf Xj :=
    (preQuotEquiv hNL W).symm.toMonoidHom.comp (β.codRestrict W hβW)
  have hψHj : Function.Surjective ψHj := by
    intro y
    have hyX : (y : MulAut ↥(chiefMod L N)) ∈ chiefAut H L N := hHj y.2
    obtain ⟨g, hg⟩ := chiefHom_surjective hHL hHN ⟨y, hyX⟩
    have hgψ : chiefPsi hHL hHN g = (y : MulAut ↥(chiefMod L N)) := congrArg Subtype.val hg
    refine ⟨⟨g, show chiefPsi hHL hHN g ∈ Hj by rw [hgψ]; exact y.2⟩, Subtype.ext ?_⟩
    exact hgψ
  have hθ's : Function.Surjective θ' := (θ.surjective.comp hψHj).comp e.symm.surjective
  have hC₀ : cSecIn Fj L Xj ≤ (chiefPsi hHL hHN).ker.map H.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro f ⟨hfF, hfc⟩
    obtain ⟨hfH, hfHj⟩ := (mem_blockPre hHL hHN Hj).1 hfF
    refine ⟨⟨f, hfH⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    refine hfaith _ hfHj fun w hw => ?_
    obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
    have hnX : (n : G) ∈ Xj := (mem_chiefPre hNL W).2 ⟨n.2, hw⟩
    exact chiefPsi_fix hHL hHN hNL (z := (n : G)) n.2 ⟨f, hfH⟩ (hfc _ hnX)
  have hker' : θ'.ker = (cSecIn Fj L Xj).subgroupOf Fj := by
    ext f
    obtain ⟨y, rfl⟩ := e.surjective f
    have hecoe : ((e y : ↥Fj) : G) = ((y : ↥H) : G) := rfl
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hecoe]
    have hθ'e : θ' (e y) = θ (ψHj y) := by
      show θ (ψHj (e.symm (e y))) = θ (ψHj y)
      rw [MulEquiv.symm_apply_apply]
    rw [hθ'e]
    constructor
    · intro h1
      have h2 : ψHj y = 1 := θ.injective (by rw [h1, map_one])
      have h3 : chiefPsi hHL hHN (y : ↥H) = 1 := congrArg Subtype.val h2
      refine Subgroup.subset_closure ⟨(e y).2, fun x hx => ?_⟩
      have hxN : x ∈ N := chiefPre_le hNL W hx
      refine comm_mem_of_chiefPsi_fix hHL hHN hNL (y : ↥H) hxN ?_
      rw [h3]
      rfl
    · intro h1
      obtain ⟨g, hg, hgy⟩ := hC₀ h1
      have hgy' : g = (y : ↥H) := Subtype.ext hgy
      have h2 : chiefPsi hHL hHN (y : ↥H) = 1 := by rw [← hgy']; exact hg
      have : ψHj y = 1 := Subtype.ext h2
      rw [this, map_one]
  have hβ's : Function.Surjective β' := by
    intro q
    obtain ⟨q', rfl⟩ := (preQuotEquiv hNL W).symm.surjective q
    have hq : (q' : ↥(chiefMod L N)) ∈ β.range := by rw [hrange]; exact q'.2
    obtain ⟨u, hu⟩ := hq
    refine ⟨u, ?_⟩
    show (preQuotEquiv hNL W).symm (β.codRestrict W hβW u) = _
    congr 1
    exact Subtype.ext hu
  have hβ'k : β'.ker = natKer m := by
    rw [natKer_eq_bot hm]
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : β.codRestrict W hβW u = 1 := by
        have : (preQuotEquiv hNL W).symm (β.codRestrict W hβW u) = 1 := h1
        exact (map_eq_one_iff _ (preQuotEquiv hNL W).symm.injective).1 this
      have h3 : β u = 1 := congrArg Subtype.val h2
      have : u ∈ β.ker := h3
      rw [hker] at this
      simpa using this
    · intro h1
      rw [h1, map_one]
  refine ⟨θ', β', hθ's, hker', hβ's, hβ'k, ?_⟩
  intro f u x hux
  obtain ⟨y, rfl⟩ := e.surjective f
  have hxN : (x : G) ∈ N := chiefPre_le hNL W x.2
  have h1 : preHom hNL W x = ⟨β u, hβW u⟩ := by
    have h0 := congrArg (preQuotEquiv hNL W) hux
    have e1 : (preQuotEquiv hNL W) (β' u) = ⟨β u, hβW u⟩ := by
      show (preQuotEquiv hNL W) ((preQuotEquiv hNL W).symm (β.codRestrict W hβW u)) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [e1, preQuotEquiv_mk] at h0
    exact h0.symm
  have h1' : chiefIota hNL ⟨(x : G), hxN⟩ = β u := congrArg Subtype.val h1
  set g : ↥H := (y : ↥H) with hg
  have hgHj : chiefPsi hHL hHN g ∈ Hj := y.2
  have hgn : (g : G) * (x : G) * (g : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hHN g.2) (x : G)).mp hxN
  have hpsi := chiefPsi_iota hHL hHN hNL g ⟨(x : G), hxN⟩ hgn
  rw [h1'] at hpsi
  have hfxX : (g : G) * (x : G) * (g : G)⁻¹ ∈ Xj := by
    refine (mem_chiefPre hNL W).2 ⟨hgn, ?_⟩
    rw [← hpsi]
    exact apply_mem_commV_of_mem hgHj (hβW u)
  refine ⟨hfxX, ?_⟩
  apply (preQuotEquiv hNL W).injective
  have e2 : (preQuotEquiv hNL W) (β' (coreAct m (θ' (e y)) u)) =
      ⟨β (coreAct m (θ' (e y)) u), hβW _⟩ := by
    show (preQuotEquiv hNL W) ((preQuotEquiv hNL W).symm (β.codRestrict W hβW _)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [e2, preQuotEquiv_mk]
  apply Subtype.ext
  show β (coreAct m (θ' (e y)) u) = chiefIota hNL ⟨(g : G) * (x : G) * (g : G)⁻¹, hgn⟩
  have hθ'e : θ' (e y) = θ (ψHj y) := by
    show θ (ψHj (e.symm (e y))) = θ (ψHj y)
    rw [MulEquiv.symm_apply_apply]
  rw [hθ'e, heq, ← hpsi]
  rfl

theorem chiefIota_comm (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (g : ↥H) {n : G} (hn : n ∈ N)
    (hgn : (g : G) * n * (g : G)⁻¹ * n⁻¹ ∈ N) :
    chiefIota hNL ⟨(g : G) * n * (g : G)⁻¹ * n⁻¹, hgn⟩ =
      chiefPsi hHL hHN g (chiefIota hNL ⟨n, hn⟩) * (chiefIota hNL ⟨n, hn⟩)⁻¹ := by
  have hgn' : (g : G) * n * (g : G)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN g.2) n).mp hn
  have e : (⟨(g : G) * n * (g : G)⁻¹ * n⁻¹, hgn⟩ : ↥N) = ⟨(g : G) * n * (g : G)⁻¹, hgn'⟩ * ⟨n, hn⟩⁻¹ :=
    rfl
  rw [e, map_mul, map_inv, chiefPsi_iota hHL hHN hNL g ⟨n, hn⟩ hgn']

theorem chiefPre_commV_eq (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (chiefMod L N)) {Hj : Subgroup (MulAut ↥(chiefMod L N))}
    (hHj : Hj ≤ chiefAut H L N) :
    chiefPre (chief_nl hstep hUH) (@commV _ (chiefCG hE) Hj) =
      ⁅N, blockPre (Setting.hHL hstep) (Setting.hHN hstep) Hj⁆ ⊔ L := by
  classical
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := chief_nl hstep hUH
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  set W : Subgroup ↥(chiefMod L N) := commV Hj with hW
  set Fj : Subgroup G := blockPre hHL hHN Hj with hFj
  apply le_antisymm
  · intro x hx
    obtain ⟨hxN, hxW⟩ := (mem_chiefPre hNL W).1 hx
    set Q : Subgroup ↥(chiefMod L N) := ((⁅N, Fj⁆).subgroupOf N).map (chiefIota hNL) with hQ
    have hWQ : W ≤ Q := by
      refine (Subgroup.closure_le Q).mpr ?_
      rintro _ ⟨y, hy, v, rfl⟩
      obtain ⟨g, hg⟩ := chiefHom_surjective hHL hHN ⟨y, hHj hy⟩
      have hgy : chiefPsi hHL hHN g = y := congrArg Subtype.val hg
      obtain ⟨n, rfl⟩ := chiefIota_surjective hNL v
      have hgF : (g : G) ∈ Fj := (mem_blockPre hHL hHN Hj).2 ⟨g.2, by
        have : (⟨(g : G), g.2⟩ : ↥H) = g := rfl
        rw [this, hgy]
        exact hy⟩
      have hgn' : (g : G) * (n : G) * (g : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hHN g.2) (n : G)).mp n.2
      have hgn : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ N := N.mul_mem hgn' (N.inv_mem n.2)
      have hmem : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ ⁅N, Fj⁆ := by
        have h1 : ⁅(n : G), (g : G)⁆ ∈ ⁅N, Fj⁆ := Subgroup.commutator_mem_commutator n.2 hgF
        have h2 := (⁅N, Fj⁆).inv_mem h1
        have e : (⁅(n : G), (g : G)⁆)⁻¹ = (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rwa [e] at h2
      refine ⟨⟨(g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹, hgn⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
      rw [chiefIota_comm hHL hHN hNL g n.2 hgn, hgy]
    obtain ⟨c, hcC, hcx⟩ := hWQ hxW
    have hcC' : (c : G) ∈ ⁅N, Fj⁆ := Subgroup.mem_subgroupOf.mp hcC
    have h1 : chiefIota hNL (c⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have h2 : (c : G)⁻¹ * x ∈ L := (chiefIota_eq_one_iff hNL _).1 h1
    have e : x = (c : G) * ((c : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hcC' h2
  · refine sup_le ?_ (le_chiefPre hNL hstep.2.2.1.le W)
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨n, hn, f, hf, rfl⟩
    obtain ⟨hfH, hfHj⟩ := (mem_blockPre hHL hHN Hj).1 hf
    set g : ↥H := ⟨f, hfH⟩ with hg
    have hgn' : f * n⁻¹ * f⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hfH) n⁻¹).mp (N.inv_mem hn)
    have hcomm : ⁅n, f⁆ ∈ N := by
      have := N.mul_mem hn hgn'
      simpa [commutatorElement_def, mul_assoc] using this
    refine (mem_chiefPre hNL W).2 ⟨hcomm, ?_⟩
    have hgen : chiefPsi hHL hHN g (chiefIota hNL ⟨n, hn⟩) * (chiefIota hNL ⟨n, hn⟩)⁻¹ ∈ W :=
      Subgroup.subset_closure ⟨_, hfHj, _, rfl⟩
    have e : chiefIota hNL ⟨⁅n, f⁆, hcomm⟩ =
        (chiefPsi hHL hHN g (chiefIota hNL ⟨n, hn⟩) * (chiefIota hNL ⟨n, hn⟩)⁻¹)⁻¹ := by
      have h1 : (⟨⁅n, f⁆, hcomm⟩ : ↥N) = ⟨n, hn⟩ * ⟨f * n⁻¹ * f⁻¹, hgn'⟩ :=
        Subtype.ext (by simp [commutatorElement_def, mul_assoc])
      rw [h1, map_mul]
      have h2 := chiefPsi_iota hHL hHN hNL g ⟨n⁻¹, N.inv_mem hn⟩ hgn'
      have h3 : chiefIota hNL ⟨n⁻¹, N.inv_mem hn⟩ = (chiefIota hNL ⟨n, hn⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h3, map_inv] at h2
      rw [mul_inv_rev, inv_inv]
      exact congrArg (fun z => chiefIota hNL ⟨n, hn⟩ * z) h2.symm
    rw [e]
    exact W.inv_mem hgen

theorem comm_mem_of_act_trivial (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (chiefMod L N)) {Hj Hk : Subgroup (MulAut ↥(chiefMod L N))}
    (hact : ∀ a ∈ Hk, ∀ v ∈ @commV _ (chiefCG hE) Hj, a v = v) :
    ∀ f ∈ blockPre (Setting.hHL hstep) (Setting.hHN hstep) Hk,
      ∀ x ∈ chiefPre (chief_nl hstep hUH) (@commV _ (chiefCG hE) Hj),
        f * x * f⁻¹ * x⁻¹ ∈ L := by
  intro f hf x hx
  obtain ⟨hfH, hfHk⟩ := (mem_blockPre _ _ Hk).1 hf
  obtain ⟨hxN, hxW⟩ := (mem_chiefPre _ _).1 hx
  exact comm_mem_of_chiefPsi_fix (Setting.hHL hstep) (Setting.hHN hstep) (chief_nl hstep hUH)
    ⟨f, hfH⟩ hxN (hact _ hfHk _ hxW)

theorem chiefPre_inf_eq (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hLN : L ≤ N)
    {W₁ W₂ : Subgroup ↥(chiefMod L N)} (h : W₁ ⊓ W₂ = ⊥) :
    chiefPre hNL W₁ ⊓ chiefPre hNL W₂ = L := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨hxN, hxW₁⟩ := (mem_chiefPre hNL W₁).1 hx1
    obtain ⟨_, hxW₂⟩ := (mem_chiefPre hNL W₂).1 hx2
    have : chiefIota hNL ⟨x, hxN⟩ ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
    rw [h, Subgroup.mem_bot] at this
    exact (chiefIota_eq_one_iff hNL ⟨x, hxN⟩).1 this
  · exact le_inf (le_chiefPre hNL hLN W₁) (le_chiefPre hNL hLN W₂)

theorem chiefPre_sup_eq (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hLN : L ≤ N)
    {W₁ W₂ : Subgroup ↥(chiefMod L N)} (h : W₁ ⊔ W₂ = ⊤) :
    chiefPre hNL W₁ ⊔ chiefPre hNL W₂ = N := by
  apply le_antisymm
  · exact sup_le (chiefPre_le hNL W₁) (chiefPre_le hNL W₂)
  · intro x hxN
    set Q : Subgroup ↥(chiefMod L N) :=
      ((chiefPre hNL W₁ ⊔ chiefPre hNL W₂).subgroupOf N).map (chiefIota hNL) with hQ
    have hWQ : W₁ ⊔ W₂ ≤ Q := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
        exact ⟨n, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ((mem_chiefPre hNL W₁).2 ⟨n.2, hw⟩)), rfl⟩
      · obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
        exact ⟨n, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ((mem_chiefPre hNL W₂).2 ⟨n.2, hw⟩)), rfl⟩
    have hx : chiefIota hNL ⟨x, hxN⟩ ∈ Q := hWQ (h ▸ Subgroup.mem_top _)
    obtain ⟨c, hc, hcx⟩ := hx
    have hc' : (c : G) ∈ chiefPre hNL W₁ ⊔ chiefPre hNL W₂ := Subgroup.mem_subgroupOf.mp hc
    have h1 : chiefIota hNL (c⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have h2 : (c : G)⁻¹ * x ∈ L := (chiefIota_eq_one_iff hNL _).1 h1
    have e : x = (c : G) * ((c : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ hc' (Subgroup.mem_sup_left (le_chiefPre hNL hLN W₁ h2))

theorem range_chiefPsi (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    (chiefPsi hHL hHN).range = chiefAut H L N := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact chiefPsi_mem hHL hHN g
  · intro hy
    obtain ⟨g, hg⟩ := chiefHom_surjective hHL hHN ⟨y, hy⟩
    exact ⟨g, congrArg Subtype.val hg⟩

theorem map_ker_chiefPsi (hstep : IsChiefStep H U L N) (hUH : U ≤ H) :
    ((chiefPsi (Setting.hHL hstep) (Setting.hHN hstep)).ker).map H.subtype = cSecIn H L N := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := chief_nl hstep hUH
  rw [cSecIn_eq_centralizerMod le_rfl hstep.2.1]
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (chiefHom_eq_one_iff hHL hHN hNL g).1 (Subtype.ext (MonoidHom.mem_ker.1 hg))
  · intro hx
    refine ⟨⟨x, hx.1⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    exact congrArg Subtype.val ((chiefHom_eq_one_iff hHL hHN hNL ⟨x, hx.1⟩).2 hx)

theorem blockPre_sup_eq (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    {H₁ H₂ : Subgroup (MulAut ↥(chiefMod L N))} (h1 : H₁ ≤ chiefAut H L N)
    (h2 : H₂ ≤ chiefAut H L N)
    (hJ : ((thompsonJ H).subgroupOf H).map (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep)) =
      H₁ ⊔ H₂) :
    blockPre (Setting.hHL hstep) (Setting.hHN hstep) H₁ ⊔
        blockPre (Setting.hHL hstep) (Setting.hHN hstep) H₂ = thompsonJ H ⊔ cSecIn H L N := by
  have hrange := range_chiefPsi (Setting.hHL hstep) (Setting.hHN hstep)
  unfold blockPre
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range _ (hrange ▸ h1) (hrange ▸ h2), ← hJ,
    Subgroup.comap_map_eq, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (B6.thompsonJ_le H),
    map_ker_chiefPsi hstep hUH]

end Block

section Two

variable {G : Type} [Group G] {H L N U : Subgroup G}

theorem translate_two (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (chiefMod L N)) {m : ℕ} (hm : Odd m)
    {T' H₁ H₂ : Subgroup (MulAut ↥(chiefMod L N))}
    {θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)} {θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)}
    {β₁ β₂ : ↥(coreMod m) →* ↥(chiefMod L N)}
    {Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥(chiefAut H L N)}
    (hd : @WreathData ↥(chiefMod L N) (chiefCG hE) (chiefAut H L N) T' m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ)
    (hJ : ((thompsonJ H).subgroupOf H).map
      (Ψ.symm.toMonoidHom.comp (chiefHom (Setting.hHL hstep) (Setting.hHN hstep))) =
      (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker) :
    QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin m) ≀ᵣ Q2)
        (Equiv.Perm (Fin m) × Equiv.Perm (Fin m)) ∧ NaturalSnPair m H L N := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := chief_nl hstep hUH
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hJ' : ((thompsonJ H).subgroupOf H).map (chiefPsi hHL hHN) = H₁ ⊔ H₂ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hmem : (Ψ.symm.toMonoidHom.comp (chiefHom hHL hHN)) x ∈
          (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker :=
        hJ ▸ ⟨x, hx, rfl⟩
      have hr : (Ψ.symm (chiefHom hHL hHN x)).right = 1 := hmem
      have := (hd.Ψmem (Ψ.symm (chiefHom hHL hHN x))).2 hr
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    · intro y hy
      have hyX : y ∈ chiefAut H L N := sup_le hd.h1X hd.h2X hy
      have hr : (Ψ.symm ⟨y, hyX⟩).right = 1 :=
        (hd.Ψmem _).1 (by rw [MulEquiv.apply_symm_apply]; exact hy)
      have hmem : Ψ.symm ⟨y, hyX⟩ ∈
          (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker := hr
      rw [← hJ] at hmem
      obtain ⟨x, hx, hxy⟩ := hmem
      refine ⟨x, hx, ?_⟩
      have : chiefHom hHL hHN x = ⟨y, hyX⟩ := Ψ.symm.injective hxy
      exact congrArg Subtype.val this
  refine ⟨⟨Ψ.symm.toMonoidHom.comp (chiefHom hHL hHN),
    Ψ.symm.surjective.comp (chiefHom_surjective hHL hHN), ?_,
    ⟨(MulEquiv.subgroupCongr hJ).trans (baseEquiv _)⟩⟩, ?_⟩
  · have hCeq : cSecIn H L N = centralizerMod L H N := cSecIn_eq_centralizerMod le_rfl hstep.2.1
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hCeq]
    constructor
    · intro hg
      have hg' : Ψ.symm (chiefHom hHL hHN g) = 1 := hg
      have h1 : chiefHom hHL hHN g = 1 := Ψ.symm.injective (by rw [map_one]; exact hg')
      exact (chiefHom_eq_one_iff hHL hHN hNL g).1 h1
    · intro hg
      have h1 := (chiefHom_eq_one_iff hHL hHN hNL g).2 hg
      show Ψ.symm (chiefHom hHL hHN g) = 1
      rw [h1, map_one]
  · have hLN : L ≤ N := hstep.2.2.1.le
    have hnorm₁ : (L.subgroupOf (chiefPre hNL (commV H₁))).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer ((chiefPre_le hNL _).trans hNL)
    have hnorm₂ : (L.subgroupOf (chiefPre hNL (commV H₂))).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer ((chiefPre_le hNL _).trans hNL)
    refine ⟨blockPre hHL hHN H₁, blockPre hHL hHN H₂, chiefPre hNL (commV H₁), chiefPre hNL (commV H₂),
      hnorm₁, hnorm₂, blockPre_le hHL hHN H₁, blockPre_le hHL hHN H₂,
      chiefPre_commV_eq hstep hUH hE hd.h1X, chiefPre_commV_eq hstep hUH hE hd.h2X,
      le_chiefPre hNL hLN _, chiefPre_le hNL _, le_chiefPre hNL hLN _, chiefPre_le hNL _,
      chiefPre_inf_eq hNL hLN hd.infV, chiefPre_sup_eq hNL hLN hd.supV,
      comm_mem_of_act_trivial hstep hUH hE hd.act₂, comm_mem_of_act_trivial hstep hUH hE hd.act₁,
      blockPre_sup_eq hstep hUH hd.h1X hd.h2X hJ', ?_, ?_⟩
    · exact naturalSn_block hstep hUH hE hm hd.h1X θ₁ β₁ hd.eq₁ hd.range₁ hd.ker₁
    · exact naturalSn_block hstep hUH hE hm hd.h2X θ₂ β₂ hd.eq₂ hd.range₂ hd.ker₂

end Two

end Ch3w

end CFSG.Quasithin
