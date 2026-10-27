module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative

@[expose] def StmtKerLUOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          ∀ x ∈ ch82LU L (ch82U (fsuV T I) h),
            x ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) →
              ∀ p : ℕ, (p = 3 ∨ p = 5) → x ^ p = 1 → x = 1

section Felem

theorem exists_orderOf_prime_map_ne_one {A B : Type} [Group A] [Group B] [Finite A]
    [IsSimpleGroup A] (π : A →* B) (hπs : Function.Surjective π) (hB : ∃ b : B, b ≠ 1)
    {p : ℕ} [hp : Fact p.Prime] (hdvd : p ∣ Nat.card A) :
    ∃ a : A, orderOf a = p ∧ π a ≠ 1 ∧ π a ^ p = 1 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨b, hb⟩ := hB
      obtain ⟨g, rfl⟩ := hπs b
      apply hb
      have hg : g ∈ π.ker := by
        rw [h]
        exact Subgroup.mem_top g
      exact MonoidHom.mem_ker.mp hg
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact hp.out.ne_one ha.symm
  refine ⟨a, ha, fun h => ha1 (hinj (h.trans (map_one π).symm)), ?_⟩
  rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]

theorem exists_mem_orderOf_of_alternatingNatural {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} (h5 : AlternatingNatural H ⊤ ⊥ 5) (hH : H ≠ ⊥) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ 60) :
    ∃ s : MulAut W, s ∈ H ∧ s ^ p = 1 ∧ s ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, hπs, -⟩ := h5
  have hcardA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hBne : ∃ b : ↥H, b ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hH
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (hcon ⟨b, hb⟩)
  let π' : ↥(alternatingGroup (Fin 5)) →* ↥H := π
  have hπ's : Function.Surjective π' := hπs
  obtain ⟨τ, -, hτ1, hτp⟩ :=
    exists_orderOf_prime_map_ne_one (p := p) π' hπ's hBne (by rw [hcardA]; exact hdvd)
  refine ⟨((π' τ : ↥H) : MulAut W), (π' τ).2, ?_, fun hs => hτ1 (Subtype.ext (hs.trans
    (OneMemClass.coe_one H).symm))⟩
  rw [← Subgroup.coe_pow, hτp, OneMemClass.coe_one]

end Felem

section FelemMain

theorem stmtFelemL3M22_holds (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal)
    (h825 : Stmt8_2_5) (hLU : HLU82) (hcard : CFSG.Quasithin.H.Mathieu.StmtH13Card)
    (hK : StmtKerLUOdd) :
    StmtFelemL3M22 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' p hpm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, -, hLN, -, hAN, hAL, hAp, hAe, -, -, -, -⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨-, h5, -, -⟩ := hlu82_82 hLU hcard hrow hL0 hV hLN hC5 hAN hAL hAp hAe
  set U := ch82U (fsuV T I) h with hUdef
  set LU := ch82LU L U with hLUdef
  set F := fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) with hFdef
  have hfix : F = U.subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  have hUV : U ≤ fsuV T I := inf_le_left
  have hA5 := h5 (hrow'.imp (fun hr => ⟨1, hr⟩) id)
  have hH0 := ne_bot_of_alternatingNatural_828 (Or.inl rfl) hA5
  have hpp : p.Prime := by rcases hpm with rfl | rfl <;> norm_num
  have hpdvd : p ∣ 60 := by rcases hpm with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨s, hsH, hsp, hs1⟩ := exists_mem_orderOf_of_alternatingNatural hA5 hH0 hpp hpdvd
  have hσ : orderOf s = p := orderOf_eq_prime hsp hs1
  obtain ⟨g, hgX, hgs⟩ := mem_autSub.mp hsH
  obtain ⟨x, hxN, hxLU, hxg⟩ := AutOn.mem_autOn_iff_exists.mp hgX
  have hR : ∀ w : ↥F, (((s w : ↥F) : ↥(fsuV T I)) : G) = x * ((w : ↥(fsuV T I)) : G) * x⁻¹ := by
    intro w
    have e1 : s w = resHom F g w := by rw [← hgs]
    rw [e1, resHom_apply, ← hxg, AutOn.coe_conjAct_apply]
  have hpow : ∀ n : ℕ, ∀ w : ↥F,
      ((((s ^ n) w : ↥F) : ↥(fsuV T I)) : G) = x ^ n * ((w : ↥(fsuV T I)) : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, MulAut.mul_apply, ih, hR w]
      group
  have hwU : ∀ w : ↥F, ((w : ↥(fsuV T I)) : G) ∈ U := by
    intro w
    obtain ⟨v, hv⟩ := w
    rw [hfix] at hv
    exact Subgroup.mem_subgroupOf.mp hv
  have toFix : ∀ u ∈ U, ∃ w : ↥F, ((w : ↥(fsuV T I)) : G) = u := by
    intro u hu
    refine ⟨⟨⟨u, hUV hu⟩, ?_⟩, rfl⟩
    rw [hfix]
    exact Subgroup.mem_subgroupOf.mpr hu
  have hxpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, r, hr, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hxpos p hpp.ne_one
  have hsn : s ^ orderOf x = 1 := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    rw [hpow (orderOf x) w, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hpn : p ∣ orderOf x := by
    have := orderOf_dvd_of_pow_eq_one hsn
    rwa [hσ] at this
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn
    rw [hn] at hpn
    exact hr hpn
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hred : ∀ m : ℕ, ∀ y : G, y ∈ LU → y ∈ Subgroup.centralizer (U : Set G) →
      y ^ p ^ m = 1 → y = 1 := by
    intro m
    induction m with
    | zero =>
      intro y _ _ hy
      simpa using hy
    | succ m ih =>
      intro y hyLU hyC hy
      have hyp1 : y ^ p = 1 := by
        apply ih (y ^ p) (Subgroup.pow_mem _ hyLU p) (Subgroup.pow_mem _ hyC p)
        rw [← pow_mul, ← pow_succ']
        exact hy
      exact hK G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' y hyLU hyC p hpm hyp1
  have hcent : ∀ w : ↥F, x ^ (p * r) * ((w : ↥(fsuV T I)) : G) * (x ^ (p * r))⁻¹ =
      ((w : ↥(fsuV T I)) : G) := by
    intro w
    rw [← hpow (p * r) w, pow_mul, hsp, one_pow]
    rfl
  have hxpLU : x ^ (p * r) ∈ LU := Subgroup.pow_mem _ hxLU _
  have hxpC : x ^ (p * r) ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨w, hw⟩ := toFix u hu
    have h1 := hcent w
    rw [hw] at h1
    have h2 : x ^ (p * r) * u = u * x ^ (p * r) := by
      calc x ^ (p * r) * u = (x ^ (p * r) * u * (x ^ (p * r))⁻¹) * x ^ (p * r) := by group
        _ = u * x ^ (p * r) := by rw [h1]
    exact h2.symm
  have hnotC : x ^ r ∉ Subgroup.centralizer (U : Set G) := by
    intro hc'
    apply hr
    have hsr : s ^ r = 1 := by
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      apply Subtype.ext
      rw [hpow r w]
      have hcw := Subgroup.mem_centralizer_iff.mp hc' _ (hwU w)
      show x ^ r * ((w : ↥(fsuV T I)) : G) * (x ^ r)⁻¹ = ((w : ↥(fsuV T I)) : G)
      rw [← hcw]
      group
    have := orderOf_dvd_of_pow_eq_one hsr
    rwa [hσ] at this
  have e2 : (x ^ r) ^ p = x ^ (p * r) := by rw [← pow_mul, mul_comm]
  refine ⟨x ^ r, Subgroup.pow_mem _ hxLU r, ?_, hnotC⟩
  rw [e2]
  have hy1 : (x ^ (p * r)) ^ p ^ a' = 1 := by
    rw [← pow_mul]
    have e : p * r * p ^ a' = orderOf x := by
      rw [hn, pow_succ]
      ring
    rw [e, pow_orderOf_eq_one]
  exact hred a' (x ^ (p * r)) hxpLU hxpC hy1

end FelemMain

end CFSG.Quasithin.H13
