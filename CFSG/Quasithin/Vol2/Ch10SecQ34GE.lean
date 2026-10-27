module

public import CFSG.Quasithin.Vol2.Ch10SecQ34GD
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts
public import CFSG.Quasithin.Vol2.Ch10SecQ34GA
public import CFSG.Quasithin.Vol2.Ch10SecQ34GC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace C10P34

variable {V : Type} [CommGroup V] {I : Fin 4 → Subgroup V} {U : Subgroup V}
  {H : Subgroup (MulAut V)} {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}

theorem card_commutator_le [Finite V] (hsup : (⊥ ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H (I i) ⊥ π) :
    Nat.card ↥(U.map (((π tau32 : ↥H) : MulAut V).toMonoidHom / MonoidHom.id V)) ≤ 16 := by
  set τ : MulAut V := ((π tau32 : ↥H) : MulAut V) with hτ
  set c : V →* V := τ.toMonoidHom / MonoidHom.id V with hc
  have hcapp : ∀ v, c v = τ v * v⁻¹ := fun v => by
    rw [hc, MonoidHom.div_apply, div_eq_mul_inv]
    rfl
  choose f hfI hf2 hfc using fun i => commutator_tau (hreal i)
  set Φ := Subgroup.noncommPiCoprod (comm_pairwise (fun i => Subgroup.zpowers (f i))) with hΦ
  have hle : U.map c ≤ Φ.range := by
    rintro _ ⟨u, hu, rfl⟩
    have huR : u ∈ (sumMap I).range := by rw [sumMap_range hsup]; exact hu
    obtain ⟨x, rfl⟩ := huR
    have hmem : ∀ i, c (x i) ∈ Subgroup.zpowers (f i) := by
      intro i
      rcases hfc i (x i) (x i).2 with h | h
      · rw [hcapp, h]
        exact Subgroup.one_mem _
      · rw [hcapp, h]
        exact Subgroup.mem_zpowers _
    refine ⟨fun i => ⟨c (x i), hmem i⟩, ?_⟩
    rw [hΦ, Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod, sumMap_apply, map_prod]
  calc Nat.card ↥(U.map c) ≤ Nat.card Φ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (∀ i, ↥(Subgroup.zpowers (f i))) :=
        Nat.card_le_card_of_surjective _ Φ.rangeRestrict_surjective
    _ = ∏ i, Nat.card ↥(Subgroup.zpowers (f i)) := Nat.card_pi
    _ ≤ ∏ _i : Fin 4, 2 := by
        refine Finset.prod_le_prod fun i _ => ?_
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hf2 i)
    _ = 16 := by norm_num

theorem stab_U (hsup : (⊥ ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H (I i) ⊥ π) :
    ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := by
  intro h hh u hu
  have huR : u ∈ (sumMap I).range := by rw [sumMap_range hsup]; exact hu
  obtain ⟨x, rfl⟩ := huR
  rw [← sumMap_range hsup]
  refine ⟨fun i => ⟨h (x i), (hreal i).2.2.2.1 ⟨h, hh⟩ _ (x i).2⟩, ?_⟩
  rw [sumMap_apply, sumMap_apply, map_prod]

end C10P34

theorem factCommGL4_holds : FactCommGL4 := by
  intro V _ _ H A U p hds hp hp2 hpH hA hAH hAU hu₀ a ha
  obtain ⟨u₀, hu₀U, hu₀1, hu₀A⟩ := hu₀
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hds
  have hcard := C10P34.card_eq_168 (hreal 0)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpH (by rw [hcard]; norm_num)
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact hpH (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have hak : a ^ p ^ k = 1 := congrArg Subtype.val hk
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  set τ : MulAut V := ((π C10P34.tau32 : ↥H) : MulAut V) with hτ
  have hτH : τ ∈ H := (π C10P34.tau32).2
  have hcomm : ∀ h ∈ H, ∀ v, a (h v) = h (a v) := fun h hh v => by
    have := congrArg (fun g : MulAut V => g v) (hAH a ha h hh)
    simpa [MulAut.mul_apply] using this
  have hHU := C10P34.stab_U hsup hreal
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => C10P34.mul_self_eq_one hsup hreal hu
  set c : V →* V := τ.toMonoidHom / MonoidHom.id V with hc
  have hcapp : ∀ v, c v = τ v * v⁻¹ := fun v => by
    rw [hc, MonoidHom.div_apply, div_eq_mul_inv]
    rfl
  set W : Subgroup V := U.map c with hW
  have hWU : W ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hcapp]
    exact U.mul_mem (hHU τ hτH u hu) (U.inv_mem hu)
  have hW16 : Nat.card ↥W ≤ 16 := C10P34.card_commutator_le hsup hreal
  have hWp : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
    exact hsq _ (hWU w.2))⟩
  have haW : ∀ w ∈ W, a w ∈ W := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨a u, hAU a ha u hu, ?_⟩
    rw [hcapp, hcapp, map_mul, map_inv, hcomm τ hτH]
  set C : Subgroup V :=
    { carrier := {u | u ∈ U ∧ a u = u}
      mul_mem' := fun {x y} hx hy => ⟨U.mul_mem hx.1 hy.1, by rw [map_mul, hx.2, hy.2]⟩
      one_mem' := ⟨U.one_mem, map_one a⟩
      inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, by rw [map_inv, hx.2]⟩ } with hC
  have hCH : ∀ h ∈ H, ∀ u ∈ C, h u ∈ C := fun h hh u hu =>
    ⟨hHU h hh u hu.1, by rw [hcomm h hh, hu.2]⟩
  obtain ⟨s, hsC, hτs⟩ : ∃ s ∈ C, τ s ≠ s := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hCU : C ≤ U := fun u hu => hu.1
    have hb := C10P34.eq_bot_of_centralized hind hsup hreal hCU hCH hcon
    have hu₀C : u₀ ∈ C := ⟨hu₀U, hu₀A a ha⟩
    rw [hb, Subgroup.mem_bot] at hu₀C
    exact hu₀1 hu₀C
  have htW : c s ∈ W := ⟨s, hsC.1, rfl⟩
  have ht1 : c s ≠ 1 := by
    rw [hcapp]
    intro h
    exact hτs (mul_inv_eq_one.mp h)
  have hat : a (c s) = c s := by rw [hcapp, map_mul, map_inv, hcomm τ hτH, hsC.2]
  set r : ↥W →* ↥W :=
    { toFun := fun w => ⟨a w, haW w w.2⟩
      map_one' := Subtype.ext (map_one a)
      map_mul' := fun x y => Subtype.ext (map_mul a (x : V) (y : V)) } with hr
  have hrinj : Function.Injective r := fun x y h =>
    Subtype.ext (a.injective (congrArg Subtype.val h))
  set ā : MulAut ↥W := MulEquiv.ofBijective r (Finite.injective_iff_bijective.mp hrinj) with hā
  have hān : ∀ n : ℕ, ∀ w : ↥W, ((ā ^ n) w : V) = (a ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      have h1 : ((ā ^ (n + 1)) w : V) = a (((ā ^ n) w : ↥W) : V) := by
        rw [pow_succ', MulAut.mul_apply]
        rfl
      rw [h1, ih, pow_succ', MulAut.mul_apply]
  have hāk : ā ^ p ^ k = 1 := MulEquiv.ext fun w => Subtype.ext (by rw [hān, hak]; rfl)
  have hā1 := C10P34.eq_one_of_card_le_sixteen hWp hW16 hp hp2 hp3 hp7 hāk
    (w₀ := ⟨c s, htW⟩) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext hat)
  have hstep1 : ∀ w ∈ W, a w = w := fun w hw =>
    congrArg (fun g : MulAut ↥W => ((g ⟨w, hw⟩ : ↥W) : V)) hā1
  set ca : V →* V := a.toMonoidHom / MonoidHom.id V with hca
  have hcaapp : ∀ v, ca v = a v * v⁻¹ := fun v => by
    rw [hca, MonoidHom.div_apply, div_eq_mul_inv]
    rfl
  set T : Subgroup V := U.map ca with hT
  have hTU : T ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hcaapp]
    exact U.mul_mem (hAU a ha u hu) (U.inv_mem hu)
  have hTH : ∀ h ∈ H, ∀ t ∈ T, h t ∈ T := by
    rintro h hh _ ⟨u, hu, rfl⟩
    refine ⟨h u, hHU h hh u hu, ?_⟩
    rw [hcaapp, hcaapp, map_mul, map_inv, hcomm h hh]
  have hTτ : ∀ t ∈ T, τ t = t := by
    intro t ht
    by_contra hτt
    have ht' : c t ∈ T := by
      rw [hcapp]
      exact T.mul_mem (hTH τ hτH t ht) (T.inv_mem ht)
    have hct1 : c t ≠ 1 := by
      rw [hcapp]
      intro h
      exact hτt (mul_inv_eq_one.mp h)
    have hfix : a (c t) = c t := hstep1 _ ⟨t, hTU ht, rfl⟩
    have hctsq : c t * c t = 1 := hsq _ (hTU ht')
    obtain ⟨v, -, hve⟩ := ht'
    have hav : a v = v * c t := by
      rw [← hve, hcaapp, mul_comm v, inv_mul_cancel_right]
    exact hct1 (C10P34.eq_one_of_fixed_commutator hodd hak hav hfix hctsq)
  have hTb := C10P34.eq_bot_of_centralized hind hsup hreal hTU hTH hTτ
  intro u hu
  have hmem : ca u ∈ T := ⟨u, hu, rfl⟩
  rw [hTb, Subgroup.mem_bot, hcaapp] at hmem
  exact mul_inv_eq_one.mp hmem

end CFSG.Quasithin.Vol2.Ch10.SecB
