module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MG
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts
public import CFSG.Quasithin.Vol2.Ch10SecQ34MA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

theorem factCommAlt5_holds : FactCommAlt5 := by
  intro V _ _ H A Z p hD hp hp2 hpH hA hcomm hZ x hx v
  obtain ⟨π, hπ⟩ := hD
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  have hH60 : Nat.card H = 60 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv]
    exact FFC.card_alt_five
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpH (by rw [hH60]; norm_num)
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact hpH (by rw [hH60]; norm_num)
  obtain ⟨B, hBs, hBk, hBe⟩ := C10P34.exists_core_hom hπ
  obtain ⟨Y, hY⟩ := C10P34.exists_induced B hBs x.toMonoidHom
    (fun w hw => (hBk _).mpr (hZ x hx w ((hBk w).mp hw)))
  have hY' : ∀ w, Y (B w) = B (x w) := hY
  have hYinj : Function.Injective Y := by
    rw [injective_iff_map_eq_one]
    intro m hm
    obtain ⟨w, rfl⟩ := hBs m
    rw [hY'] at hm
    have h1 := hZ x⁻¹ (A.inv_mem hx) _ ((hBk _).mp hm)
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    exact (hBk w).mpr h1
  set σ : MulAut ↥(G6.coreMod 5) :=
    MulEquiv.ofBijective Y ⟨hYinj, Finite.injective_iff_surjective.mp hYinj⟩ with hσ
  have hσB : ∀ w, σ (B w) = B (x w) := hY'
  have hxπ : ∀ (γ : ↥(alternatingGroup (Fin 5))) (w : V),
      x (((π γ : ↥H) : MulAut V) w) = ((π γ : ↥H) : MulAut V) (x w) := by
    intro γ w
    have := congrArg (fun g : MulAut V => g w) (hcomm x hx _ (π γ).2)
    simpa [MulAut.mul_apply] using this
  have hσc : ∀ (γ : ↥(alternatingGroup (Fin 5))) (m : ↥(G6.coreMod 5)),
      σ ⟨G6.permAct 5 (γ : Perm (Fin 5)) m, G6.permAct_mem_coreMod (γ : Perm (Fin 5)) m.2⟩ =
        ⟨G6.permAct 5 (γ : Perm (Fin 5)) (σ m),
          G6.permAct_mem_coreMod (γ : Perm (Fin 5)) (σ m).2⟩ := by
    intro γ m
    obtain ⟨w, rfl⟩ := hBs m
    have e1 : (⟨G6.permAct 5 (γ : Perm (Fin 5)) (B w),
        G6.permAct_mem_coreMod (γ : Perm (Fin 5)) (B w).2⟩ : ↥(G6.coreMod 5)) =
        B (((π γ : ↥H) : MulAut V) w) := Subtype.ext (hBe γ w).symm
    apply Subtype.ext
    show ((σ ⟨G6.permAct 5 (γ : Perm (Fin 5)) (B w),
        G6.permAct_mem_coreMod (γ : Perm (Fin 5)) (B w).2⟩ : ↥(G6.coreMod 5)) : G6.PermMod 5) =
      G6.permAct 5 (γ : Perm (Fin 5)) ((σ (B w) : ↥(G6.coreMod 5)) : G6.PermMod 5)
    rw [e1, hσB, hσB, hxπ]
    exact hBe γ (x w)
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
  have hpow : ∀ (n : ℕ) (w : V), (σ ^ n) (B w) = B ((x ^ n) w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, MulAut.mul_apply, hσB, ih, pow_succ, MulAut.mul_apply]
  have hσk : σ ^ p ^ k = 1 := by
    ext m
    obtain ⟨w, rfl⟩ := hBs m
    rw [hpow, hxk, MulAut.one_apply, MulAut.one_apply]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hσk)
  have hG : IsPGroup p ↥(Subgroup.zpowers σ) := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hmod := hG.card_modEq_card_fixedPoints ↥(G6.coreMod 5)
  set F : Subgroup ↥(G6.coreMod 5) := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id _) with hF
  have hmemF : ∀ m, m ∈ F ↔ σ m = m := fun m => Iff.rfl
  have hset : MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥(G6.coreMod 5) =
      (F : Set ↥(G6.coreMod 5)) := by
    ext m
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, hmemF]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro h g
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut ↥(G6.coreMod 5)) m :=
        Subgroup.zpowers_le.mpr h
      exact hle g.2
  have hfixF : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥(G6.coreMod 5)) =
      Nat.card F := by
    rw [hset]
    rfl
  rw [hfixF, FFC.card_coreMod_five] at hmod
  have hFdvd : Nat.card F ∣ 16 := FFC.card_coreMod_five ▸ Subgroup.card_subgroup_dvd_card F
  rcases C10P34.card_fix_cases hp hp2 hp3 hp5 hFdvd hmod with h16 | h2
  ·
    have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h16, FFC.card_coreMod_five])
    have hfix : σ (B v) = B v := (hmemF _).mp (hFtop ▸ Subgroup.mem_top (B v))
    rw [hσB] at hfix
    have h3 : B (x v * v⁻¹) = 1 := by rw [map_mul, map_inv, hfix, mul_inv_cancel]
    exact (hBk _).mp h3
  ·
    exfalso
    have hFne : F ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h2
      norm_num at h2
    obtain ⟨⟨m, hmF⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
    have hm1' : m ≠ 1 := fun h => hm1 (Subtype.ext h)
    refine C10P34.false_of_card_two h2 hmF hm1' fun c hc n hn => ?_
    have hcA : c ∈ alternatingGroup (Fin 5) := by
      rcases hc with rfl | rfl
      exacts [C10P34.mem_alt_c1, C10P34.mem_alt_c2]
    rw [hmemF] at hn ⊢
    have := hσc ⟨c, hcA⟩ n
    rw [hn] at this
    exact this

end CFSG.Quasithin.Vol2.Ch10.SecB
