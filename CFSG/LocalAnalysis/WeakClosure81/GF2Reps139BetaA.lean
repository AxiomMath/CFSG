module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  rw [Subgroup.mem_sup] at hu ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  exact ⟨x a, hA x hx a ha, x b, hB x hx b hb, (map_mul x a b).symm⟩

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) := by
  intro x hx u hu
  exact ⟨hA x hx u hu.1, hB x hx u hu.2⟩

private theorem w1369_mem_sup_left {A B : Subgroup W} {a : W} (ha : a ∈ A) : a ∈ A ⊔ B :=
  Subgroup.mem_sup.mpr ⟨a, ha, 1, B.one_mem, mul_one a⟩

private theorem w1369_mem_sup_right {A B : Subgroup W} {b : W} (hb : b ∈ B) : b ∈ A ⊔ B :=
  Subgroup.mem_sup.mpr ⟨1, A.one_mem, b, hb, one_mul b⟩

private theorem w1369_inv_mem_of_maps {U : Subgroup W} (e : MulAut W)
    (he : ∀ u ∈ U, e u ∈ U) : ∀ u ∈ U, e⁻¹ u ∈ U := by
  have hinj : Function.Injective
      (fun u : ↥U => (⟨e (u : W), he (u : W) u.2⟩ : ↥U)) := by
    intro u v huv
    exact Subtype.ext (e.injective (congrArg Subtype.val huv))
  have hsurj := Finite.surjective_of_injective hinj
  intro u hu
  obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
  have hvu : e (v : W) = u := congrArg Subtype.val hv
  rw [← hvu]
  simp

private theorem w1369_stableUnder_zpowers_of_maps {U : Subgroup W} {e : MulAut W}
    (he : ∀ u ∈ U, e u ∈ U) : StableUnder (Subgroup.zpowers e) U := by
  let T : Subgroup (MulAut W) :=
    { carrier := {g | ∀ u ∈ U, g u ∈ U}
      one_mem' := by intro u hu; simpa using hu
      mul_mem' := by
        intro a b ha hb u hu
        simpa [MulAut.mul_apply] using ha (b u) (hb u hu)
      inv_mem' := by
        intro a ha
        exact w1369_inv_mem_of_maps a ha }
  have hle : Subgroup.zpowers e ≤ T := Subgroup.zpowers_le.mpr he
  exact fun g hg u hu => hle hg u hu

private theorem w1369_stableUnder_map_of_commute {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hM : StableUnder K M) {g : MulAut W} (hg : ∀ k ∈ K, k * g = g * k) :
    StableUnder K (M.map g.toMonoidHom) := by
  intro k hk y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  have hkm : k (g m) = g (k m) := by
    have h := congrArg (fun f : MulAut W => f m) (hg k hk)
    simpa [MulAut.mul_apply] using h
  exact Subgroup.mem_map.mpr ⟨k m, hM k hk m hm, hkm.symm⟩

private theorem w1369_stableUnder_map_of_normalizes {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hM : StableUnder K M) {g : MulAut W}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) :
    StableUnder K (M.map g.toMonoidHom) := by
  intro k hk y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  have hk' : k ∈ K.map (MulAut.conj g).toMonoidHom := by rw [hg]; exact hk
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hk'
  refine Subgroup.mem_map.mpr ⟨a m, hM a ha m hm, ?_⟩
  have hak : g * a = k * g := by
    have h : g * a * g⁻¹ = k := by
      change (MulAut.conj g) a = k at hae
      rwa [MulAut.conj_apply] at hae
    calc g * a = (g * a * g⁻¹) * g := by group
      _ = k * g := by rw [h]
  have h := congrArg (fun f : MulAut W => f m) hak
  simpa [MulAut.mul_apply] using h

private theorem w1369_sq_apply (hw2 : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (w : W) : x (x w) = x w * w := by
  have h := mulAut_norm_mul_eq_one hx3 hfix w
  have h2 : x (x w) * (x w * w) = 1 := by
    rw [← mul_assoc]
    exact h
  have h3 : x (x w) = (x w * w)⁻¹ := mul_eq_one_iff_eq_inv.mp h2
  have hxw : (x w)⁻¹ = x w := by
    have h1 : (x w) * (x w) = 1 := by simpa [pow_two] using hw2 (x w)
    exact (mul_eq_one_iff_eq_inv.mp h1).symm
  have hw : w⁻¹ = w := by
    have h1 : w * w = 1 := by simpa [pow_two] using hw2 w
    exact (mul_eq_one_iff_eq_inv.mp h1).symm
  rw [h3, mul_inv_rev, hxw, hw]
  exact mul_comm _ _

theorem Std139.beta_split (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hnirr : ¬ IsIrrOn K ⊤ ⊥) :
    ∃ (M : Subgroup W) (x : MulAut W), x ∈ X ∧ x ≠ 1 ∧ IsIrrOn K M ⊥ ∧
      M ⊓ M.map x.toMonoidHom = ⊥ ∧ M ⊔ M.map x.toMonoidHom = ⊤ ∧ rk ↥M = n := by
  classical
  obtain ⟨x, hxgen, hx3, hx1, hfixX, -⟩ := Std139.exists_gen hw2 S
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hfixx : fixV (Subgroup.zpowers x) = ⊥ := by rw [← hxgen]; exact hfixX
  have hsq : ∀ m : W, x (x m) = x m * m := fun m => w1369_sq_apply hw2 hx3 hfixx m
  have hcardW : 1 < Nat.card W := by
    rw [S.card]
    calc 1 < 4 ^ 3 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have htopne : (⊤ : Subgroup W) ≠ ⊥ := by
    intro h
    have hc : Nat.card W = 1 := by
      rw [← Subgroup.card_top (G := W), h, Subgroup.card_bot]
    omega
  have hbotlt : (⊥ : Subgroup W) < ⊤ := bot_lt_iff_ne_bot.mpr htopne
  have hnotall : ¬ ∀ J : Subgroup W, StableUnder K J → (⊥ : Subgroup W) ≤ J →
      J ≤ ⊤ → J = ⊥ ∨ J = ⊤ := by
    intro hall
    exact hnirr ⟨hbotlt, (fun _ _ _ _ => Subgroup.mem_top _),
      (fun _ _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]), hall⟩
  have hex : ∃ J : Subgroup W, StableUnder K J ∧ J ≠ ⊥ ∧ J ≠ ⊤ := by
    by_contra h
    apply hnotall
    intro J hJ _ _
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · right
      by_contra hJtop
      exact h ⟨J, hJ, hJbot, hJtop⟩
  obtain ⟨J, hJstable, hJne, -⟩ := hex
  obtain ⟨M, hMmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun U : Subgroup W => StableUnder K U ∧ U ≠ ⊥) (fun U => Nat.card U)
    ⟨J, hJstable, hJne⟩
  have hMK : StableUnder K M := hMmin.1.1
  have hMne : M ≠ ⊥ := hMmin.1.2
  have hMcard : ∀ U : Subgroup W, StableUnder K U → U ≠ ⊥ → Nat.card M ≤ Nat.card U :=
    fun U hU hUne => hMmin.le ⟨hU, hUne⟩
  have hMirr : IsIrrOn K M ⊥ := by
    refine ⟨bot_lt_iff_ne_bot.mpr hMne, hMK, ?_, ?_⟩
    · intro k _ u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · intro C hC _ hCM
      by_cases hC0 : C = ⊥
      · exact Or.inl hC0
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge hCM (hMcard C hC hC0))
  have hKx : ∀ k ∈ K, k * x = x * k := fun k hk =>
    Std139.component_commutes_X S hK.comp k hk x hxX
  have hxMK : StableUnder K (M.map x.toMonoidHom) :=
    w1369_stableUnder_map_of_commute hMK hKx
  have hKU : StableUnder K (M ⊔ M.map x.toMonoidHom) :=
    w1369_stableUnder_sup hMK hxMK
  have hSx : StableUnder (Subgroup.zpowers x) (M ⊔ M.map x.toMonoidHom) := by
    apply w1369_stableUnder_zpowers_of_maps
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact w1369_mem_sup_right (Subgroup.mem_map_of_mem x.toMonoidHom ha)
    · obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hb
      change x (x m) ∈ M ⊔ M.map x.toMonoidHom
      rw [hsq m]
      exact Subgroup.mul_mem _
        (w1369_mem_sup_right (Subgroup.mem_map_of_mem x.toMonoidHom hm))
        (w1369_mem_sup_left hm)
  have hSX : StableUnder X (M ⊔ M.map x.toMonoidHom) := by
    intro g hg u hu
    exact hSx g (by rwa [hxgen] at hg) u hu
  have hsup_eq_top : M ⊔ M.map x.toMonoidHom = ⊤ := by
    rcases hK.irr.2.2.2 (M ⊔ M.map x.toMonoidHom) hKU hSX le_top with h | h
    · exfalso
      exact hMne (le_bot_iff.mp (le_sup_left.trans (le_of_eq h)))
    · exact h
  have hdisj : M ⊓ M.map x.toMonoidHom = ⊥ := by
    have hKinf : StableUnder K (M ⊓ M.map x.toMonoidHom) :=
      w1369_stableUnder_inf hMK hxMK
    rcases hMirr.2.2.2 (M ⊓ M.map x.toMonoidHom) hKinf bot_le inf_le_left with h | h
    · exact h
    · exfalso
      have hMle : M ≤ M.map x.toMonoidHom := (le_of_eq h.symm).trans inf_le_right
      have hcardx : Nat.card ↥(M.map x.toMonoidHom) = Nat.card ↥M :=
        Subgroup.card_map_of_injective x.injective
      have hMeq : M = M.map x.toMonoidHom :=
        Subgroup.eq_of_le_of_card_ge hMle (by rw [hcardx])
      have hxM : ∀ m ∈ M, x m ∈ M := by
        intro m hm
        have h : x m ∈ M.map x.toMonoidHom := Subgroup.mem_map_of_mem x.toMonoidHom hm
        rw [← hMeq] at h
        exact h
      have hXM : StableUnder X M := by
        have hz := w1369_stableUnder_zpowers_of_maps hxM
        intro g hg
        exact hz g (by rwa [hxgen] at hg)
      have hMtop : M = ⊤ := by
        rcases hK.irr.2.2.2 M hMK hXM le_top with hbot | htop
        · exact absurd hbot hMne
        · exact htop
      exact hnirr (hMtop ▸ hMirr)
  have hcardx : Nat.card ↥(M.map x.toMonoidHom) = Nat.card ↥M :=
    Subgroup.card_map_of_injective x.injective
  have hcard : Nat.card ↥M * Nat.card ↥M = Nat.card W := by
    have h := card_sup_mul_card_inf M (M.map x.toMonoidHom)
    rw [hsup_eq_top, hdisj, Subgroup.card_bot, Subgroup.card_top, hcardx] at h
    simpa using h.symm
  have hposM : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
  have hrkM : rk ↥M = n := by
    have hpadic : 2 * rk ↥M = rk W := by
      unfold rk
      rw [← hcard, padicValNat.mul hposM hposM]
      ring
    have hrkW : rk W = 2 * n := by
      unfold rk
      rw [S.card]
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_mul, padicValNat.prime_pow]
    omega
  exact ⟨M, x, hxX, hx1, hMirr, hdisj, hsup_eq_top, hrkM⟩

theorem Std139.beta_cost (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) {M : Subgroup W} {x : MulAut W}
    (hM : IsIrrOn K M ⊥) (hx : x ∈ X) (hx1 : x ≠ 1) (hsum : M ⊔ M.map x.toMonoidHom = ⊤)
    (hint : M ⊓ M.map x.toMonoidHom = ⊥) {e : MulAut W} (he : e ∈ D) (he1 : e ≠ 1) :
    (∀ m ∈ M, e m ∈ M) ∧ rk ↥(commSub M (Subgroup.zpowers e)) = 1 ∧
      fixV (Subgroup.zpowers e) ⊓ M = Y ⊓ M := by
  classical
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h] at hM
    exact (lt_irrefl (⊥ : Subgroup W)) hM.1
  have hcardx : Nat.card ↥(M.map x.toMonoidHom) = Nat.card ↥M :=
    Subgroup.card_map_of_injective x.injective
  have hcard : Nat.card ↥M * Nat.card ↥M = Nat.card W := by
    have h := card_sup_mul_card_inf M (M.map x.toMonoidHom)
    rw [hsum, hint, Subgroup.card_bot, Subgroup.card_top, hcardx] at h
    simpa using h.symm
  have hposM : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
  have hrkM : rk ↥M = n := by
    have hpadic : 2 * rk ↥M = rk W := by
      unfold rk
      rw [← hcard, padicValNat.mul hposM hposM]
      ring
    have hrkW : rk W = 2 * n := by
      unfold rk
      rw [S.card]
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_mul, padicValNat.prime_pow]
    omega
  have hKnorm : K.map (MulAut.conj e).toMonoidHom = K := hK.normal e (S.DG he)
  have hKeM : StableUnder K (M.map e.toMonoidHom) :=
    w1369_stableUnder_map_of_normalizes hM.2.1 hKnorm
  have hKinf : StableUnder K (M.map e.toMonoidHom ⊓ M) :=
    w1369_stableUnder_inf hKeM hM.2.1
  have hEmap : M.map e.toMonoidHom = M := by
    by_contra hne
    have hEinf : M.map e.toMonoidHom ⊓ M = ⊥ := by
      rcases hM.2.2.2 (M.map e.toMonoidHom ⊓ M) hKinf bot_le inf_le_right with h | h
      · exact h
      · exfalso
        have hMle : M ≤ M.map e.toMonoidHom := (le_of_eq h.symm).trans inf_le_left
        have hcarde : Nat.card ↥(M.map e.toMonoidHom) = Nat.card ↥M :=
          Subgroup.card_map_of_injective e.injective
        have hMeq : M = M.map e.toMonoidHom :=
          Subgroup.eq_of_le_of_card_ge hMle (by rw [hcarde])
        exact hne hMeq.symm
    let φ : ↥M → ↥(commSub ⊤ (Subgroup.zpowers e)) := fun m =>
      ⟨e (m : W) * (m : W)⁻¹,
        Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, (m : W), Subgroup.mem_top _, rfl⟩⟩
    have hφinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      have h1 : commHom e (a : W) = commHom e (b : W) := by
        have hab' : e (a : W) * (a : W)⁻¹ = e (b : W) * (b : W)⁻¹ :=
          congrArg Subtype.val hab
        rw [commHom_apply, commHom_apply]
        exact hab'
      have h2 : commHom e ((a : W) * (b : W)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 : (a : W) * (b : W)⁻¹ ∈ fixV (Subgroup.zpowers e) := by
        rw [← ker_commHom e]
        exact h2
      have h3fix : e ((a : W) * (b : W)⁻¹) = (a : W) * (b : W)⁻¹ :=
        mem_fixV_zpowers_iff.mp h3
      have hmemM : (a : W) * (b : W)⁻¹ ∈ M := M.mul_mem a.2 (M.inv_mem b.2)
      have hmemeM : (a : W) * (b : W)⁻¹ ∈ M.map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(a : W) * (b : W)⁻¹, hmemM, h3fix⟩
      have hbot : (a : W) * (b : W)⁻¹ ∈ (⊥ : Subgroup W) := by
        rw [← hEinf]
        exact ⟨hmemeM, hmemM⟩
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
    have hcard_le : Nat.card ↥M ≤
        Nat.card ↥(commSub ⊤ (Subgroup.zpowers e)) :=
      Nat.card_le_card_of_injective φ hφinj
    have hcommcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers e)) = 4 := by
      rw [card_eq_two_pow hw2 (commSub ⊤ (Subgroup.zpowers e)),
        (Std139.commSub_axis hw2 S he he1).1]
      norm_num
    have hMcard : Nat.card ↥M = 2 ^ n := by
      rw [card_eq_two_pow hw2 M, hrkM]
    rw [hMcard, hcommcard] at hcard_le
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hMstab : ∀ m ∈ M, e m ∈ M := by
    intro m hm
    have := Subgroup.mem_map_of_mem e.toMonoidHom hm
    rwa [hEmap] at this
  have hMe : StableUnder (Subgroup.zpowers e) M :=
    w1369_stableUnder_zpowers_of_maps hMstab
  have hxMX : StableUnder (Subgroup.zpowers e) (M.map x.toMonoidHom) := by
    apply w1369_stableUnder_zpowers_of_maps
    intro u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    have hxe : e * x = x * e := S.DX e he x hx
    have hex : e (x m) = x (e m) := by
      have := congrArg (fun f : MulAut W => f m) hxe
      simpa [MulAut.mul_apply] using this
    exact ⟨e m, hMstab m hm, hex.symm⟩
  have hWcomm : commSub ⊤ (Subgroup.zpowers e) = commSub M (Subgroup.zpowers e) ⊔
      commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) := by
    calc commSub ⊤ (Subgroup.zpowers e)
        = (⊤ : Subgroup W).map (commHom e) :=
          commSub_zpowers_eq_map (fun _ _ w _ => Subgroup.mem_top w)
      _ = ((M ⊔ M.map x.toMonoidHom).map (commHom e)) := by rw [hsum]
      _ = M.map (commHom e) ⊔ (M.map x.toMonoidHom).map (commHom e) :=
          Subgroup.map_sup M (M.map x.toMonoidHom) (commHom e)
      _ = commSub M (Subgroup.zpowers e) ⊔
            commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) := by
          rw [← commSub_zpowers_eq_map hMe, ← commSub_zpowers_eq_map hxMX]
  have hxcomm : commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) =
      (commSub M (Subgroup.zpowers e)).map x.toMonoidHom := by
    rw [commSub_zpowers_eq_map hxMX, commSub_zpowers_eq_map hMe,
      Subgroup.map_map (K := M) (g := commHom e) (f := x.toMonoidHom),
      Subgroup.map_map (K := M) (g := x.toMonoidHom) (f := commHom e)]
    congr 1
    ext m
    simp only [MonoidHom.comp_apply]
    rw [commHom_apply, commHom_apply, map_mul, map_inv]
    change e (x m) * (x m)⁻¹ = x (e m) * (x m)⁻¹
    have hxe : e * x = x * e := S.DX e he x hx
    have hex : e (x m) = x (e m) := by
      have := congrArg (fun f : MulAut W => f m) hxe
      simpa [MulAut.mul_apply] using this
    rw [hex]
  have hinf : commSub M (Subgroup.zpowers e) ⊓
      commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) = ⊥ := by
    have h1 : commSub M (Subgroup.zpowers e) ≤ M := commSub_le_of_invariant hMe
    have h2 : commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) ≤ M.map x.toMonoidHom :=
      commSub_le_of_invariant hxMX
    have hle : commSub M (Subgroup.zpowers e) ⊓
        commSub (M.map x.toMonoidHom) (Subgroup.zpowers e) ≤ ⊥ := by
      rw [← hint]
      exact inf_le_inf h1 h2
    exact le_bot_iff.mp hle
  have hrke : rk ↥(commSub M (Subgroup.zpowers e)) = 1 := by
    have hsup_rk := rk_sup_add_rk_inf (commSub M (Subgroup.zpowers e))
      (commSub (M.map x.toMonoidHom) (Subgroup.zpowers e))
    rw [← hWcomm, hinf, rk_bot] at hsup_rk
    have hcard_eq : rk ↥(commSub (M.map x.toMonoidHom) (Subgroup.zpowers e)) =
        rk ↥(commSub M (Subgroup.zpowers e)) := by
      rw [hxcomm]
      unfold rk
      rw [Subgroup.card_map_of_injective x.injective]
    rw [hcard_eq] at hsup_rk
    have hcomm_rk : rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 2 :=
      (Std139.commSub_axis hw2 S he he1).1
    omega
  refine ⟨hMstab, hrke, ?_⟩
  rw [Std139.fixV_eq_axis hw2 S he he1]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
