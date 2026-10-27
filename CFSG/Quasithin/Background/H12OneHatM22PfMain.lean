module

public import CFSG.Quasithin.Background.H12OneHatM22PfTrans
public import CFSG.Quasithin.Background.H12OneHatM22PfSyl
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.H12OneHatM22

public section

namespace CFSG.Quasithin.H.Mathieu.H12Pf

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu.H12Cert CFSG.QuasithinUnique
  CFSG.Quasithin.H13.MatNCert
open scoped Pointwise

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem fix_iff_of_T0 {ψ : ↥G ≃* ↥L}
    {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)} (hψθ : IsModelPair ψ θ) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ t : ↥G, ((ψ t : ↥L) : MulAut W) ∈ T ↔ (t : GL (Fin 12) (ZMod 2)) ∈ T0)
    (w : W) : (∀ t ∈ T, t w = w) ↔ Multiplicative.toAdd (θ w) ∈ F0v := by
  rw [← fix_T0_iff]
  constructor
  · intro h t ht
    have h1 := hψθ ⟨t, T0_le_G ht⟩ w
    rw [h ((ψ ⟨t, T0_le_G ht⟩ : ↥L) : MulAut W) ((hT _).mpr ht)] at h1
    exact h1.symm
  · intro h t ht
    obtain ⟨g, hg⟩ := ψ.surjective ⟨t, hTL ht⟩
    have hgT : (g : GL (Fin 12) (ZMod 2)) ∈ T0 := (hT g).mp (by rw [hg]; exact ht)
    have h1 := hψθ g w
    rw [h _ hgT, hg] at h1
    exact θ.injective (Multiplicative.toAdd.injective h1)

theorem toAdd_θ_zL {ψ : ↥G ≃* ↥L} {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
    (hψθ : IsModelPair ψ θ) (w : W) :
    Multiplicative.toAdd (θ (((ψ ⟨zU, zU_mem⟩ : ↥L) : MulAut W) w)) =
      ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (Multiplicative.toAdd (θ w)) :=
  hψθ ⟨zU, zU_mem⟩ w

theorem toAdd_eq_zero_iff {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {w : W} :
    Multiplicative.toAdd (θ w) = 0 ↔ w = 1 := by
  rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff]

theorem eq_of_mem_F0v {ψ : ↥G ≃* ↥L} {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
    (hψθ : IsModelPair ψ θ) {w : W} (hw : Multiplicative.toAdd (θ w) ∈ F0v) :
    w = 1 ∨ w = θ.symm (Multiplicative.ofAdd w0) ∨
      w = ((ψ ⟨zU, zU_mem⟩ : ↥L) : MulAut W) (θ.symm (Multiplicative.ofAdd w0)) ∨
      w = ((ψ ⟨zU, zU_mem⟩ : ↥L) : MulAut W)
        (((ψ ⟨zU, zU_mem⟩ : ↥L) : MulAut W) (θ.symm (Multiplicative.ofAdd w0))) := by
  have hθ0 : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w0))) = w0 := by simp
  have key : ∀ u : W, Multiplicative.toAdd (θ w) = Multiplicative.toAdd (θ u) → w = u :=
    fun u h => θ.injective (Multiplicative.toAdd.injective h)
  rcases (mem_F0v_iff _).mp hw with h | h | h | h
  · exact Or.inl (toAdd_eq_zero_iff.mp h)
  · exact Or.inr (Or.inl (key _ (by rw [h, hθ0])))
  · exact Or.inr (Or.inr (Or.inl (key _ (by rw [h, toAdd_θ_zL hψθ, hθ0]))))
  · exact Or.inr (Or.inr (Or.inr (key _ (by rw [h, toAdd_θ_zL hψθ, toAdd_θ_zL hψθ, hθ0]))))

theorem card_F0v : Nat.card F0v = 4 := by
  have hnd : f0.Nodup := by decide +kernel
  have hlt : ∀ c ∈ f0, c < 2 ^ 12 := f0_lt
  let e : F0v ≃ {c // c ∈ f0} :=
    { toFun := fun v => ⟨codeN v.1, by
        obtain ⟨c, hc, hv⟩ := v.2
        rw [hv, codeN_vecN (hlt c hc)]
        exact hc⟩
      invFun := fun c => ⟨vecN 12 c.1, c.1, c.2, rfl⟩
      left_inv := fun v => Subtype.ext (vecN_codeN v.1)
      right_inv := fun c => Subtype.ext (codeN_vecN (hlt c.1 c.2)) }
  rw [Nat.card_congr e,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := f0) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd,
    z12_facts.2.2.2.2.2]
  rfl

theorem stmtH12_1HatM22_holds :
    StmtH12_1HatM22 := by
  intro W _ _ hV X L S hLX hXN hCX hM hS hXLS hsz
  obtain ⟨s₀, hs₀, z₀, hz₀, hsz₀⟩ := hsz
  have hirr := isIrrSec_of_mhat22Twelve hV hM
  have hL := isHat_of_mhat22Twelve hM
  obtain ⟨ψ₀, θ₀, h₀⟩ := exists_model_of_mhat22Twelve hV hM
  have hcardL : Nat.card L = 1330560 := by rw [← Nat.card_congr ψ₀.toEquiv, card_G]
  have hTcard := card_inf_eq hLX hXN hS hXLS hcardL
  obtain ⟨ψ, θ, hψθ, hT⟩ := exists_isModelPair_T0 h₀ (inf_le_right : S ⊓ L ≤ L) hTcard
  have hSX : S ≤ X := hS.1
  have hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl =>
    (Subgroup.mem_normalizer_iff.mp (hXN (hSX hs)) l).mp hl
  have hSL' : ∀ s ∈ S, ∀ l ∈ L, s⁻¹ * l * s ∈ L := fun s hs l hl => by
    simpa using hSL s⁻¹ (S.inv_mem hs) l hl
  set inF : W → Prop := fun w => Multiplicative.toAdd (θ w) ∈ F0v with hinF
  have hfixT := fix_iff_of_T0 hψθ (inf_le_right : S ⊓ L ≤ L) hT
  obtain ⟨w₀', hw₀'⟩ : ∃ w : W, w = θ.symm (Multiplicative.ofAdd w0) := ⟨_, rfl⟩
  have hθw₀' : Multiplicative.toAdd (θ w₀') = w0 := by
    rw [hw₀', MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hw₀'F : inF w₀' := by
    show Multiplicative.toAdd (θ w₀') ∈ F0v
    rw [hθw₀']
    exact w0_mem_F0v
  have hw₀'1 : w₀' ≠ 1 := by
    intro h
    have : Multiplicative.toAdd (θ w₀') = 0 := toAdd_eq_zero_iff.mpr h
    rw [hθw₀'] at this
    exact absurd (congrFun this 0) (by decide)
  have hSF : ∀ s ∈ S, ∀ w, inF w → inF ((s : MulAut W) w) := by
    intro s hs w hw
    refine (hfixT _).mp fun t ht => ?_
    have ht' : s⁻¹ * t * s ∈ S ⊓ L :=
      ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) ht.1) hs, hSL' s hs t ht.2⟩
    have := (hfixT w).mpr hw _ ht'
    calc t (s w) = s ((s⁻¹ * t * s) w) := by simp [MulAut.mul_apply]
      _ = s w := by rw [this]
  have hSF' : ∀ s ∈ S, ∀ w, inF ((s : MulAut W) w) → inF w := by
    intro s hs w hw
    have := hSF s⁻¹ (S.inv_mem hs) _ hw
    simpa [MulAut.mul_apply] using this
  obtain ⟨zL, hzL⟩ : ∃ z : ↥L, z = ψ ⟨zU, zU_mem⟩ := ⟨_, rfl⟩
  have hzLc : zL ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨g, rfl⟩ := ψ.surjective l
    have hcomm : g * ⟨zU, zU_mem⟩ = ⟨zU, zU_mem⟩ * g := Subtype.ext (zU_comm g.2)
    rw [hzL, ← map_mul, ← map_mul, hcomm]
  have hzF : ∀ x ∈ Subgroup.center ↥L, ∀ w, inF w → inF ((x : MulAut W) w) := by
    intro x hx w hw
    refine (hfixT _).mp fun t ht => ?_
    have hc := congrArg (fun y : ↥L => (y : MulAut W) w)
      (Subgroup.mem_center_iff.mp hx ⟨t, ht.2⟩)
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at hc
    rw [hc, (hfixT w).mpr hw t ht]
  have hzLfix : ∀ w, ((zL : ↥L) : MulAut W) w = w → w = 1 := by
    intro w hw
    have h1 := toAdd_θ_zL hψθ w
    rw [← hzL, hw] at h1
    exact toAdd_eq_zero_iff.mp (eq_zero_of_zU_fix h1.symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let FS : SubMulAction ↥S W :=
    { carrier := {w | inF w}
      smul_mem' := fun s w hw => hSF s s.2 w hw }
  have hcardFS : Nat.card ↥FS = 4 := by
    rw [← card_F0v]
    exact Nat.card_congr
      { toFun := fun w => ⟨Multiplicative.toAdd (θ w.1), w.2⟩
        invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v.1), by
          show inF _
          simp [hinF, v.2]⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  have hfixFS : ∀ w : ↥(fixV S), inF (w : W) := fun w =>
    (hfixT w.1).mp fun t ht => w.2 t ht.1
  have hfixcard : Nat.card ↑(MulAction.fixedPoints ↥S ↥FS) = Nat.card ↥(fixV S) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, fun s hs => congrArg Subtype.val (x.2 ⟨s, hs⟩)⟩
        invFun := fun w => ⟨⟨w.1, hfixFS w⟩, fun s => Subtype.ext (w.2 s s.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hmod := IsPGroup.card_modEq_card_fixedPoints hS.2.1 ↥FS
  rw [hcardFS, hfixcard] at hmod
  have hle4 : Nat.card ↥(fixV S) ≤ 4 := by
    rw [← hcardFS]
    exact Nat.card_le_card_of_injective (fun w => (⟨w.1, hfixFS w⟩ : ↥FS))
      fun a b h => Subtype.ext (congrArg (fun x : ↥FS => (x : W)) h)
  have hpos : 0 < Nat.card ↥(fixV S) := Nat.card_pos
  have hall : Nat.card ↥(fixV S) = 4 → ∀ w, inF w → ∀ s ∈ S, (s : MulAut W) w = w := by
    intro h4 w hw s hs
    let ι : ↥(fixV S) → ↥FS := fun x => ⟨x.1, hfixFS x⟩
    have hinj : Function.Injective ι := fun a b h =>
      Subtype.ext (congrArg (fun x : ↥FS => (x : W)) h)
    have hsurj := (hinj.bijective_of_nat_card_le (by rw [hcardFS, h4])).2
    obtain ⟨x, hx⟩ := hsurj ⟨w, hw⟩
    have hxw : (x : W) = w := congrArg Subtype.val hx
    rw [← hxw]
    exact x.2 s hs
  have hne4 : Nat.card ↥(fixV S) ≠ 4 := by
    intro h4
    have hfix0 := hall h4
    apply hsz₀
    have hcL : s₀ * (z₀ : MulAut W) * s₀⁻¹ ∈ L := hSL s₀ hs₀ _ z₀.2
    have hcc : (⟨_, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl' : s₀⁻¹ * (l : MulAut W) * s₀ ∈ L := hSL' s₀ hs₀ _ l.2
      have hz' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨_, hl'⟩)
      simp only [Subgroup.coe_mul] at hz' ⊢
      calc (l : MulAut W) * (s₀ * z₀ * s₀⁻¹) = s₀ * ((s₀⁻¹ * l * s₀) * z₀) * s₀⁻¹ := by group
        _ = s₀ * (z₀ * (s₀⁻¹ * l * s₀)) * s₀⁻¹ := by rw [hz']
        _ = (s₀ * z₀ * s₀⁻¹) * l := by group
    have hx : (z₀⁻¹ * ⟨_, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := mul_mem (inv_mem hz₀) hcc
    by_contra hne
    have hx1 : (z₀⁻¹ * ⟨_, hcL⟩ : ↥L) ≠ 1 := by
      intro h
      apply hne
      have := congrArg Subtype.val (inv_mul_eq_one.mp h)
      exact this.symm
    apply hw₀'1
    apply HM22.fpf_of_central hirr hx hx1 w₀'
    have h1 : (s₀⁻¹ : MulAut W) w₀' = w₀' := hfix0 w₀' hw₀'F s₀⁻¹ (S.inv_mem hs₀)
    have h2 : s₀ ((z₀ : MulAut W) w₀') = (z₀ : MulAut W) w₀' :=
      hfix0 _ (hzF z₀ hz₀ w₀' hw₀'F) s₀ hs₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, MulAut.inv_apply] at h1 ⊢
    rw [h1, h2]
    simp
  have hcard2 : Nat.card ↥(fixV S) = 2 := by
    have := hmod.symm
    unfold Nat.ModEq at this
    omega
  have hzL1 : zL ≠ 1 := by
    intro h
    have h2 : ψ ⟨zU, zU_mem⟩ = ψ 1 := by rw [map_one, ← h, hzL]
    have h3 : ((⟨zU, zU_mem⟩ : ↥G) : GL (Fin 12) (ZMod 2)) =
        ((1 : ↥G) : GL (Fin 12) (ZMod 2)) := congrArg Subtype.val (ψ.injective h2)
    rw [Subgroup.coe_one] at h3
    exact zU_ne_one h3
  have hconjc : ∀ s ∈ S, ∀ x ∈ Subgroup.center ↥L, ∀ h : s⁻¹ * (x : MulAut W) * s ∈ L,
      (⟨_, h⟩ : ↥L) ∈ Subgroup.center ↥L := by
    intro s hs x hx h
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl' : s * (l : MulAut W) * s⁻¹ ∈ L := hSL s hs _ l.2
    have hz' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨_, hl'⟩)
    simp only [Subgroup.coe_mul] at hz' ⊢
    calc (l : MulAut W) * (s⁻¹ * x * s) = s⁻¹ * ((s * l * s⁻¹) * x) * s := by group
      _ = s⁻¹ * (x * (s * l * s⁻¹)) * s := by rw [hz']
      _ = (s⁻¹ * x * s) * l := by group
  set RL := toL ψ R0 with hRL
  have hRLL : RL ≤ L := toL_le ψ R0
  have hcardRL : Nat.card RL = 1152 := by rw [hRL, card_toL ψ R0_le_G, card_R0]
  have hTRL : S ⊓ L ≤ RL := by
    intro x hx
    obtain ⟨g, hg⟩ := ψ.surjective ⟨x, hx.2⟩
    rw [hRL, mem_toL]
    exact ⟨g, T0_le_R0 ((hT g).mp (by rw [hg]; exact hx)), by rw [hg]⟩
  have hcenterRL : ∀ x ∈ Subgroup.center ↥L, (x : MulAut W) ∈ RL := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_of_center hL.2.1 hx hzLc hzL1
    rw [Subgroup.coe_zpow]
    refine RL.zpow_mem ?_ k
    rw [hRL, mem_toL]
    exact ⟨⟨zU, zU_mem⟩, zU_mem_R0, by rw [hzL]⟩
  obtain ⟨y, hy⟩ : ∃ y : MulAut W, y = ((ψ ⟨y0U, R0_le_G y0U_mem_R0⟩ : ↥L) : MulAut W) :=
    ⟨_, rfl⟩
  have hyRL : y ∈ RL := mem_toL.mpr ⟨⟨y0U, R0_le_G y0U_mem_R0⟩, y0U_mem_R0, hy.symm⟩
  have hy_move : ¬ inF (y w₀') := by
    intro h
    apply y0U_not_mem
    have h1 := hψθ ⟨y0U, R0_le_G y0U_mem_R0⟩ w₀'
    rw [hθw₀', ← hy] at h1
    rw [← h1]
    exact h
  have hy_comm : ∀ w, y ((zL : MulAut W) w) = (zL : MulAut W) (y w) := by
    intro w
    have hc : (⟨y0U, R0_le_G y0U_mem_R0⟩ : ↥G) * ⟨zU, zU_mem⟩ =
        ⟨zU, zU_mem⟩ * ⟨y0U, R0_le_G y0U_mem_R0⟩ := Subtype.ext (zU_comm (R0_le_G y0U_mem_R0))
    have := congrArg (fun g : ↥G => ((ψ g : ↥L) : MulAut W) w) hc
    simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply] at this
    rw [hzL, hy]
    exact this
  have hzinv : ∀ w, inF ((zL : MulAut W) w) → inF w := by
    intro w hw
    have := hzF zL⁻¹ (inv_mem hzLc) _ hw
    simpa [MulAut.mul_apply] using this
  have hy_out : ∀ u, inF u → u ≠ 1 → ¬ inF (y u) := by
    intro u hu hu1 hyu
    rcases eq_of_mem_F0v hψθ hu with h | h | h | h
    · exact hu1 h
    · rw [← hw₀'] at h
      rw [h] at hyu
      exact hy_move hyu
    · rw [← hw₀', ← hzL] at h
      rw [h, hy_comm] at hyu
      exact hy_move (hzinv _ hyu)
    · rw [← hw₀', ← hzL] at h
      rw [h, hy_comm, hy_comm] at hyu
      exact hy_move (hzinv _ (hzinv _ hyu))
  have hsNorm : ∀ s ∈ S, ∀ x ∈ RL, s * x * s⁻¹ ∈ RL := by
    intro s hs
    set R' := RL.map (MulAut.conj s).toMonoidHom with hR'
    have hR'L : R' ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hSL s hs x (hRLL hx)
    have hconj_mem : ∀ x ∈ RL, s * x * s⁻¹ ∈ R' := fun x hx => ⟨x, hx, rfl⟩
    have hmem' : ∀ x, s⁻¹ * x * s ∈ RL → x ∈ R' := by
      intro x hx
      have := hconj_mem _ hx
      simpa [mul_assoc] using this
    have hsys : s * y * s⁻¹ ∈ L := hSL s hs y (hRLL hyRL)
    obtain ⟨g'', hg''⟩ := ψ.surjective ⟨_, hsys⟩
    have hR'' : fromL ψ R' = R0 := by
      refine eq_R0_of (fromL_le ψ R') ?_ ?_ ?_ (y := (g'' : GL (Fin 12) (ZMod 2))) ?_ ?_
      · intro t ht
        rw [mem_fromL]
        refine ⟨T0_le_G ht, hmem' _ (hTRL ?_)⟩
        have hx := (hT ⟨t, T0_le_G ht⟩).mpr ht
        exact ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hx.1) hs, hSL' s hs _ hx.2⟩
      · rw [mem_fromL]
        refine ⟨zU_mem, hmem' _ ?_⟩
        rw [← hzL]
        exact hcenterRL _ (hconjc s hs zL hzLc (hSL' s hs _ zL.2))
      · rw [card_fromL ψ hR'L, hR', Subgroup.card_map_of_injective (MulAut.conj s).injective,
          hcardRL]
      · rw [mem_fromL]
        refine ⟨g''.2, ?_⟩
        have : (⟨(g'' : GL (Fin 12) (ZMod 2)), g''.2⟩ : ↥G) = g'' := rfl
        rw [this, hg'']
        exact hconj_mem _ hyRL
      · intro hin
        have h1 := hψθ g'' w₀'
        rw [hθw₀', hg''] at h1
        have h2 : inF ((s * y * s⁻¹ : MulAut W) w₀') := by
          show Multiplicative.toAdd (θ _) ∈ F0v
          rw [h1]
          exact hin
        simp only [MulAut.mul_apply] at h2
        have hsw : inF ((s⁻¹ : MulAut W) w₀') := hSF s⁻¹ (S.inv_mem hs) _ hw₀'F
        have hsw1 : (s⁻¹ : MulAut W) w₀' ≠ 1 := by
          intro h
          apply hw₀'1
          have := congrArg (fun v => (s : MulAut W) v) h
          simpa using this
        exact hy_out _ hsw hsw1 (hSF' s hs _ h2)
    have hR'eq : R' = RL := by rw [← toL_fromL ψ hR'L, hR'']
    intro x hx
    rw [← hR'eq]
    exact hconj_mem x hx
  have hSN : S ≤ Subgroup.normalizer (RL : Set (MulAut W)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hsNorm s hs x, fun hx => ?_⟩
    have := hsNorm s⁻¹ (S.inv_mem hs) _ hx
    simpa [mul_assoc] using this
  refine ⟨hcard2, RL ⊔ S, le_sup_right, sup_le (hRLL.trans hLX) hSX, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (le_sup_left : RL ≤ RL ⊔ S) (hcenterRL x hx)
  · have hPN : RL ⊔ S ≤ Subgroup.normalizer (RL : Set (MulAut W)) :=
      sup_le Subgroup.le_normalizer hSN
    have hN : (RL.subgroupOf (RL ⊔ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hPN
    have hsolR : Group.IsSolvable ↥(RL.subgroupOf (RL ⊔ S)) := by
      have hc : Nat.card ↥(RL.subgroupOf (RL ⊔ S)) = 2 ^ 7 * 3 ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hcardRL]
        norm_num
      have := Fintype.ofFinite ↥(RL.subgroupOf (RL ⊔ S))
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hc)
    have hsolQ : Group.IsSolvable (↥(RL ⊔ S) ⧸ RL.subgroupOf (RL ⊔ S)) := by
      have : Group.IsNilpotent ↥S := hS.2.1.isNilpotent
      let f : ↥S →* ↥(RL ⊔ S) ⧸ RL.subgroupOf (RL ⊔ S) :=
        (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)
      have hf : Function.Surjective f := by
        intro q
        obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ q
        have hp : (p : MulAut W) ∈ (RL : Set (MulAut W)) * (S : Set (MulAut W)) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left RL S hSN]
          exact p.2
        obtain ⟨r, hr, s, hs, hrs⟩ := Set.mem_mul.mp hp
        refine ⟨⟨s, hs⟩, ?_⟩
        simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [← hrs]
        have := hsNorm s⁻¹ (S.inv_mem hs) r hr
        simpa [mul_assoc] using this
      exact Group.isSolvable_of_surjective hf
    exact Group.isSolvable_of_subgroup_quotient (RL.subgroupOf (RL ⊔ S))
  · intro Y hY4 hYfix hYz hPY
    have : Nontrivial ↥(fixV S) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard2]; norm_num)
    obtain ⟨⟨w₁, hw₁⟩, hw₁1⟩ := exists_ne (1 : ↥(fixV S))
    have hw₁1' : w₁ ≠ 1 := fun h => hw₁1 (Subtype.ext h)
    have hw₁F : inF w₁ := hfixFS ⟨w₁, hw₁⟩
    have hz3 : ∀ w, (zL : MulAut W) ((zL : MulAut W) ((zL : MulAut W) w)) = w := by
      intro w
      have h3 : zL ^ 3 = 1 := by
        rw [hzL, ← map_pow]
        have : (⟨zU, zU_mem⟩ : ↥G) ^ 3 = 1 := Subtype.ext zU_pow_three
        rw [this, map_one]
      have := congrArg (fun x : ↥L => (x : MulAut W) w) h3
      simpa [pow_succ, MulAut.mul_apply] using this
    have hzw : (zL : MulAut W) w₁ ≠ w₁ := fun h => hw₁1' (hzLfix w₁ h)
    have hz1 : ∀ w, (zL : MulAut W) w = 1 → w = 1 := fun w h => by
      have := congrArg (fun v => (zL : MulAut W)⁻¹ v) h
      simpa using this
    have hw₁Y : w₁ ∈ Y := hYfix hw₁
    have hzw₁Y : (zL : MulAut W) w₁ ∈ Y := hYz zL hzLc w₁ hw₁Y
    have hzzw₁Y : (zL : MulAut W) ((zL : MulAut W) w₁) ∈ Y := hYz zL hzLc _ hzw₁Y
    have hYeq : ∀ v ∈ Y, v = 1 ∨ v = w₁ ∨ v = (zL : MulAut W) w₁ ∨
        v = (zL : MulAut W) ((zL : MulAut W) w₁) := by
      classical
      have := Fintype.ofFinite W
      let A : Finset W := {1, w₁, (zL : MulAut W) w₁, (zL : MulAut W) ((zL : MulAut W) w₁)}
      have hne1 : (1 : W) ≠ w₁ := fun h => hw₁1' h.symm
      have hne2 : (1 : W) ≠ (zL : MulAut W) w₁ := fun h => hw₁1' (hz1 _ h.symm)
      have hne3 : (1 : W) ≠ (zL : MulAut W) ((zL : MulAut W) w₁) :=
        fun h => hw₁1' (hz1 _ (hz1 _ h.symm))
      have hne4' : w₁ ≠ (zL : MulAut W) w₁ := fun h => hzw h.symm
      have hne5 : w₁ ≠ (zL : MulAut W) ((zL : MulAut W) w₁) := fun h => hzw (by
        have := congrArg (fun v => (zL : MulAut W) v) h
        rw [hz3] at this
        exact this)
      have hne6 : (zL : MulAut W) w₁ ≠ (zL : MulAut W) ((zL : MulAut W) w₁) :=
        fun h => hzw ((zL : MulAut W).injective h).symm
      have hA : A.card = 4 := by
        simp [A, Finset.card_insert_of_notMem, hne1, hne2, hne3, hne4', hne5, hne6]
      have hAY : A ⊆ (Y : Set W).toFinset := by
        intro v hv
        rw [Set.mem_toFinset]
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact Y.one_mem
        · exact hw₁Y
        · exact hzw₁Y
        · exact hzzw₁Y
      have hYc : (Y : Set W).toFinset.card = 4 := by
        rw [← Nat.card_eq_card_toFinset]
        exact hY4
      have hAeq := Finset.eq_of_subset_of_card_le hAY (by rw [hA, hYc])
      intro v hv
      have : v ∈ A := by rw [hAeq, Set.mem_toFinset]; exact hv
      simpa [A] using this
    have hw₀'Y : w₀' ∈ Y := by
      rcases eq_of_mem_F0v hψθ hw₁F with h | h | h | h
      · exact absurd h hw₁1'
      · rw [← hw₀'] at h
        rw [← h]
        exact hw₁Y
      · rw [← hw₀', ← hzL] at h
        have : w₀' = (zL : MulAut W) ((zL : MulAut W) w₁) := by rw [h, hz3]
        rw [this]
        exact hzzw₁Y
      · rw [← hw₀', ← hzL] at h
        have : w₀' = (zL : MulAut W) w₁ := by rw [h, hz3]
        rw [this]
        exact hzw₁Y
    have hyY := hPY y ((le_sup_left : RL ≤ RL ⊔ S) hyRL) w₀' hw₀'Y
    apply hy_move
    rcases hYeq _ hyY with h | h | h | h <;> rw [h]
    · show Multiplicative.toAdd (θ 1) ∈ F0v
      rw [map_one, toAdd_one]
      exact zero_mem_F0v
    · exact hw₁F
    · exact hzF zL hzLc _ hw₁F
    · exact hzF zL hzLc _ (hzF zL hzLc _ hw₁F)

end CFSG.Quasithin.H.Mathieu.H12Pf
