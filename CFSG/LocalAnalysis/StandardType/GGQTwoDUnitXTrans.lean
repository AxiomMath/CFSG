module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTransA
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

private theorem qtwoDB20_coordBlockSU_le_erase {J : Finset (Fin m)}
    (hJ : J ⊆ Finset.univ.erase c) :
    coordBlockSU F0 2 1 J ≤ coordBlockSU F0 2 1 (Finset.univ.erase c) := by
  intro A hA
  rw [mem_coordBlockSU_iff] at hA ⊢
  intro i j hij
  exact hA i j (hij.imp (fun h hiJ => h (hJ hiJ)) (fun h hjJ => h (hJ hjJ)))

private theorem qtwoDB20_map_conj_self {X : Subgroup G} {n : G} (hn : n ∈ X) :
    X.map (MulAut.conj n).toMonoidHom = X := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hn hx) (X.inv_mem hn)
  · intro y hy
    refine ⟨n⁻¹ * y * n, X.mul_mem (X.mul_mem (X.inv_mem hn) hy) hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem qtwoDB20_suPairBlock_le_erase {u v : Fin m}
    (hu : u ∈ Finset.univ.erase c) (hv : v ∈ Finset.univ.erase c) :
    ggSuPairBlock F0 2 1 m u v ≤ coordBlockSU F0 2 1 (Finset.univ.erase c) := by
  intro A hA
  rw [mem_coordBlockSU_iff]
  intro i j hij
  have hne : (i ≠ u ∧ i ≠ v) ∨ (j ≠ u ∧ j ≠ v) := by
    rcases hij with hi | hj
    · left
      have hic : i = c := by
        by_contra h
        exact hi (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)
      subst hic
      exact ⟨fun h => (Finset.mem_erase.mp hu).1 h.symm,
        fun h => (Finset.mem_erase.mp hv).1 h.symm⟩
    · right
      have hjc : j = c := by
        by_contra h
        exact hj (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
      subst hjc
      exact ⟨fun h => (Finset.mem_erase.mp hu).1 h.symm,
        fun h => (Finset.mem_erase.mp hv).1 h.symm⟩
  rw [hA i j hne, Matrix.one_apply]

private theorem qtwoDB20_normal_form_pair (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b')
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hrC : r ∈ ggCoxRefl M e) (hr'A : r' ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hr'C : r' ∈ ggCoxRefl M e) (hnc : r * r' ≠ r' * r) :
    ∃ (p₀ p₁ p₂ : Fin m) (n : G) (a₀ : MulAut ↥Bs),
      p₁.val = p₀.val + 1 ∧ p₂.val = p₀.val + 2 ∧
      c ≠ p₀ ∧ c ≠ p₁ ∧ c ≠ p₂ ∧
      n ∈ qtwoDelX ψ c g ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ s : ↥Bs, ((a₀ s : ↥Bs) : G) = n * (s : G) * n⁻¹) ∧
      a₀ * r * a₀⁻¹ = ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∧
      a₀ * r' * a₀⁻¹ = ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
  classical
  have hXc := qtwoDB20_X_le_centralizer hbase hcoords hdel
  have hrb' : r b' = b' := qtwoDB20_fixes_b' hXc hrA
  have hr'b' : r' b' = b' := qtwoDB20_fixes_b' hXc hr'A
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoords.coxRoot r hrC
  obtain ⟨sgn', i', j', hi'j', hact'⟩ := hcoords.coxRoot r' hr'C
  have hfix : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hdel.coord] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB20_dTau_fixes_single hij hfix
  have hfix' : dTau m sgn' i' j' (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r' b')) = βL (Additive.ofMul b') := by rw [hr'b']
    rw [hact' b', hdel.coord] at h1
    exact h1
  obtain ⟨hci', hcj'⟩ := qtwoDB20_dTau_fixes_single hi'j' hfix'
  have hnc' : dTau m sgn i j * dTau m sgn' i' j' ≠ dTau m sgn' i' j' * dTau m sgn i j := by
    intro h
    apply hnc
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    simp only [MulAut.mul_apply, hact, hact']
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (βL (Additive.ofMul s))) h
  obtain ⟨p₀, p₁, p₂, V', hp1, hp2, hc0, hc1, hc2, hV'mem, hV'fix', hV'conj1, hV'conj2⟩ :=
    qtwoDB20_normal_form_pair_lin (by omega) hij hi'j' hci hcj hci' hcj' hnc'
  obtain ⟨a₀, ha₀J, ha₀V'⟩ := hcoords.join_onto V' hV'mem
  have ha₀X : a₀ ∈ ggAutomizer (qtwoDelX ψ c g) Bs :=
    ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign hdel.norm
      hdel.conj ha₀J hV'mem hV'fix' ha₀V'
  obtain ⟨n, hnX, hnN, hnact⟩ := mem_ggAutomizer_iff.mp ha₀X
  have hainv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) = V'⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h := ha₀V' (a₀⁻¹ s)
    rw [show a₀ (a₀⁻¹ s) = s from MulEquiv.apply_symm_apply a₀ s] at h
    calc βL (Additive.ofMul (a₀⁻¹ s))
        = V'⁻¹ (V' (βL (Additive.ofMul (a₀⁻¹ s)))) :=
          (LinearEquiv.symm_apply_apply V' _).symm
      _ = V'⁻¹ (βL (Additive.ofMul s)) := congrArg (fun x => V'⁻¹ x) h.symm
  refine ⟨p₀, p₁, p₂, n, a₀, hp1, hp2, hc0, hc1, hc2, hnX, hnN, hnact, ?_, ?_⟩
  · refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m =>
      T (βL (Additive.ofMul s))) hV'conj1
    have h1 : βL (Additive.ofMul ((a₀ * r * a₀⁻¹) s)) =
        V' (dTau m sgn i j (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact, hainv s]
    have h2 : βL (Additive.ofMul
        ((((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s))) =
        dPerm m (Equiv.swap p₀ p₁) (βL (Additive.ofMul s)) :=
      hcoords.perm (Equiv.swap p₀ p₁) s
    rw [h1, h2]
    simpa only [LinearEquiv.mul_apply, qtwoDB20_dTau_false] using hcomp
  · refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m =>
      T (βL (Additive.ofMul s))) hV'conj2
    have h1 : βL (Additive.ofMul ((a₀ * r' * a₀⁻¹) s)) =
        V' (dTau m sgn' i' j' (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact', hainv s]
    have h2 : βL (Additive.ofMul
        ((((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s))) =
        dPerm m (Equiv.swap p₁ p₂) (βL (Additive.ofMul s)) :=
      hcoords.perm (Equiv.swap p₁ p₂) s
    rw [h1, h2]
    simpa only [LinearEquiv.mul_apply, qtwoDB20_dTau_false] using hcomp
theorem ggQTwoDUnit_X_rankOne (hL1 : GGQTwoL1Input) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    ∀ r ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r ∈ ggCoxRefl M e →
      ggRankOne Bs r = ggRankOneIn (qtwoDelX ψ c g) Bs r := by
  intro r hrA hrC
  classical
  have hXc : qtwoDelX ψ c g ≤ Subgroup.centralizer ({(b' : G)} : Set G) :=
    qtwoDB20_X_le_centralizer hbase hcoords hdel
  have hrb' : r b' = b' := qtwoDB20_fixes_b' hXc hrA
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoords.coxRoot r hrC
  have hsingle : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hdel.coord] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB20_dTau_fixes_single hij hsingle
  obtain ⟨w, hwEven, hwfix, u, v, huErase, hvErase, huv, hwconj⟩ :=
    qtwoDB20_normal_form_one (by omega) hij hci hcj
  obtain ⟨a₀, ha₀J, ha₀w⟩ := hcoords.join_onto w hwEven
  have ha₀X : a₀ ∈ ggAutomizer (qtwoDelX ψ c g) Bs :=
    ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign hdel.norm
      hdel.conj ha₀J hwEven hwfix ha₀w
  obtain ⟨n, hnX, -, hnact⟩ := mem_ggAutomizer_iff.mp ha₀X
  have ha₀w_inv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) = w⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h : w (βL (Additive.ofMul (a₀⁻¹ s))) = βL (Additive.ofMul s) := by
      have h' := ha₀w (a₀⁻¹ s)
      rw [MulAut.apply_inv_self] at h'
      exact h'.symm
    rw [← h]
    simpa using (LinearEquiv.symm_apply_apply w (βL (Additive.ofMul (a₀⁻¹ s)))).symm
  let r₀ : MulAut ↥Bs := a₀ * r * a₀⁻¹
  have hr₀_act : ∀ s : ↥Bs, βL (Additive.ofMul (r₀ s)) =
      dTau m false u v (βL (Additive.ofMul s)) := by
    intro s
    have h1 : r₀ s = a₀ (r (a₀⁻¹ s)) := by simp only [r₀, MulAut.mul_apply]
    rw [h1, ha₀w (r (a₀⁻¹ s)), hact (a₀⁻¹ s), ha₀w_inv s]
    rw [show dTau m false u v = w * dTau m sgn i j * w⁻¹ from hwconj.symm]
    rfl
  have hr₀_eq : r₀ = ((ε (Equiv.swap u v) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    rw [hr₀_act s, hcoords.perm (Equiv.swap u v) s]
    simp [dTau]
  have hr₀L : r₀ ∈ ggAutomizer L Bs := by
    rw [hr₀_eq]
    exact (ε (Equiv.swap u v)).2
  have hr₀Cox : r₀ ∈ ggCoxRefl M e :=
    hcoords.cox false u v huv r₀ (Subgroup.mem_sup_left hr₀L) hr₀_act
  have hEq₀ : ggRankOne Bs r₀ = ggRankOneIn (qtwoDelX ψ c g) Bs r₀ := by
    have hL1r₀ : ggRankOne Bs r₀ = ggRankOneIn L Bs r₀ :=
      (hL1 G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) r₀ hr₀L hr₀Cox).1
    have hgr : ggRankOne Bs r₀ = (ggSuPairBlock F0 2 1 m u v).map ψ := by
      rw [hL1r₀, hr₀_eq]
      exact hbase.rankOne u v huv
    have hSu_le : (ggSuPairBlock F0 2 1 m u v).map ψ ≤ qtwoDelJ ψ c :=
      Subgroup.map_mono (qtwoDB20_suPairBlock_le_erase huErase hvErase)
    have hXle : ggRankOne Bs r₀ ≤ qtwoDelX ψ c g := by
      rw [hgr]
      exact hSu_le.trans le_sup_left
    have hmono : ggOTwoPrime (qtwoDelX ψ c g ⊓
        Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) ≤
        ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) :=
      LinFusion.ggOTwoPrime_mono inf_le_right
    have hXinf : ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) ≤
        qtwoDelX ψ c g ⊓ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G) := by
      intro x hx
      exact ⟨hXle hx, ggOTwoPrime_le _ hx⟩
    show ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) =
      ggOTwoPrime (qtwoDelX ψ c g ⊓ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G))
    exact le_antisymm (qtwoDB20_oTwoPrime_le_inf hXinf) hmono
  have hnX_inv : n⁻¹ ∈ qtwoDelX ψ c g := (qtwoDelX ψ c g).inv_mem hnX
  have hnact_inv : ∀ s : ↥Bs, ((a₀⁻¹ s : ↥Bs) : G) = n⁻¹ * (s : G) * n⁻¹⁻¹ := by
    intro s
    have h := hnact (a₀⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  have hmap := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom) hEq₀
  rw [ggRankOne_map_conj hnact_inv r₀, ggRankOneIn_map_conj hnact_inv r₀,
    qtwoDB20_map_conj_self hnX_inv] at hmap
  have hr_eq : a₀⁻¹ * r₀ * a₀ = r := by
    rw [show r₀ = a₀ * r * a₀⁻¹ from rfl]
    group
  rw [inv_inv] at hmap
  rw [hr_eq] at hmap
  exact hmap
theorem ggQTwoDUnit_X_rankTwo (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    ∀ r ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r ∈ ggCoxRefl M e →
      ∀ r' ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r' ∈ ggCoxRefl M e → r * r' ≠ r' * r →
        ggRankTwo Bs r r' = ggRankTwoIn (qtwoDelX ψ c g) Bs r r' := by
  intro r hrA hrC r' hr'A hr'C hnc
  classical
  obtain ⟨p₀, p₁, p₂, n, a₀, hp1, hp2, hc0, hc1, hc2, hnX, -, hnact, heq1, heq2⟩ :=
    qtwoDB20_normal_form_pair hm hbase hcoords hdel hrA hrC hr'A hr'C hnc
  have hp0p1 : p₀ ≠ p₁ := fun h => by have := congrArg Fin.val h; omega
  have hp1p2 : p₁ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  have hp0p2 : p₀ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  set e₁ : MulAut ↥Bs := (((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) with he₁
  set e₂ : MulAut ↥Bs := (((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) with he₂
  have heA₁ : e₁ ∈ ggAutomizer L Bs := by rw [he₁]; exact (ε (Equiv.swap p₀ p₁)).2
  have heA₂ : e₂ ∈ ggAutomizer L Bs := by rw [he₂]; exact (ε (Equiv.swap p₁ p₂)).2
  have heC₁ : e₁ ∈ ggCoxRefl M e := by
    rw [he₁]
    exact hcoords.cox false p₀ p₁ hp0p1
      (((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (Subgroup.mem_sup_left (ε (Equiv.swap p₀ p₁)).2) (fun s => by
        rw [hcoords.perm]; simp [dTau])
  have heC₂ : e₂ ∈ ggCoxRefl M e := by
    rw [he₂]
    exact hcoords.cox false p₁ p₂ hp1p2
      (((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (Subgroup.mem_sup_left (ε (Equiv.swap p₁ p₂)).2) (fun s => by
        rw [hcoords.perm]; simp [dTau])
  have henc : e₁ * e₂ ≠ e₂ * e₁ := by
    intro h
    apply hnc
    have hr1 : a₀⁻¹ * e₁ * a₀ = r := by rw [← heq1]; group
    have hr2 : a₀⁻¹ * e₂ * a₀ = r' := by rw [← heq2]; group
    calc r * r' = (a₀⁻¹ * e₁ * a₀) * (a₀⁻¹ * e₂ * a₀) := by rw [hr1, hr2]
      _ = a₀⁻¹ * (e₁ * e₂) * a₀ := by group
      _ = a₀⁻¹ * (e₂ * e₁) * a₀ := by rw [h]
      _ = (a₀⁻¹ * e₂ * a₀) * (a₀⁻¹ * e₁ * a₀) := by group
      _ = r' * r := by rw [hr1, hr2]
  have hEA_L : ggRankTwo Bs e₁ e₂ = ggRankTwoIn L Bs e₁ e₂ :=
    hEA G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) e₁ heA₁ heC₁ e₂ heA₂ heC₂ henc
  have hrank : ggRankTwoIn L Bs e₁ e₂ =
      (coordBlockSU F0 2 1 ({p₀, p₁, p₂} : Finset (Fin m))).map ψ := by
    rw [← hbase.range]
    exact ggQTwoDUnit_rankTwoIn_eq (K := F0) hbase.hyp hbase.card_field hbase.diag
      hp0p1 hp1p2 hp0p2
      (fun s => by rw [he₁]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₀ p₁) s)
      (fun s => by rw [he₂]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₁ p₂) s)
  have hJsub : ({p₀, p₁, p₂} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl
    · exact ⟨hc0.symm, Finset.mem_univ _⟩
    · exact ⟨hc1.symm, Finset.mem_univ _⟩
    · exact ⟨hc2.symm, Finset.mem_univ _⟩
  have hgr : ggRankTwo Bs e₁ e₂ =
      (coordBlockSU F0 2 1 ({p₀, p₁, p₂} : Finset (Fin m))).map ψ := by
    rw [hEA_L, hrank]
  have hXle : ggRankTwo Bs e₁ e₂ ≤ qtwoDelX ψ c g := by
    rw [hgr]
    exact (Subgroup.map_mono (qtwoDB20_coordBlockSU_le_erase hJsub)).trans le_sup_left
  have hmono : ggOTwoPrime (qtwoDelX ψ c g ⊓ Subgroup.centralizer
      ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) ≤
      ggOTwoPrime (Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) :=
    LinFusion.ggOTwoPrime_mono inf_le_right
  have hXinf : ggOTwoPrime (Subgroup.centralizer
      ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) ≤
      qtwoDelX ψ c g ⊓ Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G) := by
    intro x hx
    exact ⟨hXle hx, ggOTwoPrime_le _ hx⟩
  have hEq₀ : ggRankTwo Bs e₁ e₂ = ggRankTwoIn (qtwoDelX ψ c g) Bs e₁ e₂ := by
    show ggOTwoPrime (Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) =
      ggOTwoPrime (qtwoDelX ψ c g ⊓ Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G))
    exact le_antisymm (qtwoDB20_oTwoPrime_le_inf hXinf) hmono
  have hnX_inv : n⁻¹ ∈ qtwoDelX ψ c g := (qtwoDelX ψ c g).inv_mem hnX
  have hnact_inv : ∀ s : ↥Bs, ((a₀⁻¹ s : ↥Bs) : G) = n⁻¹ * (s : G) * n⁻¹⁻¹ := by
    intro s
    have h := hnact (a₀⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  have hmap := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom) hEq₀
  rw [ggRankTwo_map_conj hnact_inv e₁ e₂, ggRankTwoIn_map_conj hnact_inv e₁ e₂,
    qtwoDB20_map_conj_self hnX_inv] at hmap
  have he₁r : a₀⁻¹ * e₁ * a₀ = r := by rw [← heq1]; group
  have he₂r : a₀⁻¹ * e₂ * a₀ = r' := by rw [← heq2]; group
  rw [inv_inv] at hmap
  rw [he₁r, he₂r] at hmap
  exact hmap
end CFSG.StandardType.QTwo
end
