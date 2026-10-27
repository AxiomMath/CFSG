module

public import CFSG.Quasithin.Vol2.Ch10SecB3Gen
public import CFSG.Quasithin.Vol2.Ch10SecB3Ind

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

namespace L32

theorem pa_pow_twelve : ∀ g : Γ, IsPa g → g ^ 12 = 1 := by unfold IsPa ent; decide +kernel

theorem pb_pow_twelve : ∀ g : Γ, IsPb g → g ^ 12 = 1 := by unfold IsPb ent; decide +kernel

theorem eq_top_of_lt {A A' : Subgroup Γ} (hA : A = Pa ∨ A = Pb) (h : A < A') : A' = ⊤ := by
  have hU : U3 ≤ A' := by
    rcases hA with rfl | rfl
    · exact u3_le_pa.trans h.le
    · exact u3_le_pb.trans h.le
  rcases overgroups A' hU with h' | h' | h' | h'
  · exfalso
    rcases hA with rfl | rfl
    · exact pa_not_le_u3 (h' ▸ h.le)
    · exact pb_not_le_u3 (h' ▸ h.le)
  · exfalso
    rcases hA with rfl | rfl
    · exact h.ne h'.symm
    · exact pb_not_le_pa (h' ▸ h.le)
  · exfalso
    rcases hA with rfl | rfl
    · exact pa_not_le_pb (h' ▸ h.le)
    · exact h.ne h'.symm
  · exact h'

end L32

variable {G : Type} [Group G]

theorem odd_prime_dvd_of_L32 {Q : Type*} [Group Q] (e : Q ≃* L32.Γ) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (MulAut Q) → r ∣ Nat.card Q := by
  intro r hr hr2 hd
  rw [card_mulAut_of_equiv_SL32 e, show (336 : ℕ) = 2 * 168 by norm_num] at hd
  rw [Nat.card_congr e.toEquiv, card_Γ]
  rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) hr2
  · exact h

theorem eq_one_of_mem_of_odd {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · exact absurd (hj ▸ Nat.even_pow.mpr ⟨even_two, by omega⟩) (Nat.not_even_iff_odd.mpr hodd)

variable [Finite G] {T L I : Subgroup G}

theorem le_fsuM_of_le (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {X : Subgroup G}
    (hX : fsuL0 T L ⊔ T ≤ X) (hX2 : pCoreOf 2 X ≠ ⊥) : X ≤ fsuM T L := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hX2
  have h := (isUniqueM_L0T h331 hyp).2 M' ⟨hM'.1, hX.trans hM'.2⟩
  rw [← h]
  exact hM'.2

theorem not_le_of_isHStar (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : ¬ L ≤ H := by
  intro hLH
  have hL0 : fsuL0 T L ≤ H := conjClosure_le fun s hs l hl =>
    H.mul_mem (H.mul_mem (hH.1.1 hs) (hLH hl)) (H.inv_mem (hH.1.1 hs))
  exact hH.2.1 (le_fsuM_of_le h331 hyp (sup_le hL0 hH.1.1) hH.1.2)

structure Ctx3 (T L I H B : Subgroup G) (t : G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ)
    (α : MulAut L32.Γ) (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ) : Prop where
  h37 : Vol2Native.A37ForSQTKCat
  h38 : Vol2Native.A38ForSQTKCat
  h322 : TmpL6_3_2_2_two
  h331 : Stmt3_3_1
  h1013 : Stmt10_1_3
  hyp : Hyp10 G T L I
  hH : IsHStar T (fsuM T L) H
  hfaith : HallFaithful T L I H
  hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  hC : L0CoordG T L t Ψ α ψ

omit [Finite G] in
theorem isMaxSubgroupIn_map {K N : Subgroup G} (e : G ≃* G) (h : IsMaxSubgroupIn K N) :
    IsMaxSubgroupIn (K.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  have hid' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => e.apply_symm_apply x
  refine ⟨(Subgroup.map_lt_map_iff_of_injective e.injective).mpr h.1, fun J hJ hJK => ?_⟩
  have h1 : N < J.map e.symm.toMonoidHom := by
    have := (Subgroup.map_lt_map_iff_of_injective (f := e.symm.toMonoidHom) e.symm.injective).mpr hJ
    rwa [Subgroup.map_map, hid, Subgroup.map_id] at this
  have h2 : J.map e.symm.toMonoidHom ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hJK hy
    simpa using hz
  rw [← h.2 _ h1 h2, Subgroup.map_map, hid', Subgroup.map_id]

omit [Finite G] in
theorem isMax_preIn_inf_L {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
    {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ} (hC : L0CoordG T L t Ψ α ψ)
    {A : Subgroup L32.Γ} (hA : A = L32.Pa ∨ A = L32.Pb) :
    IsMaxSubgroupIn L (preIn Ψ (A.prod A) ⊓ L) := by
  have hmem : ∀ (l : G) (hl : l ∈ L), l ∈ preIn Ψ (A.prod A) ↔ ψ (mkO2 L l hl) ∈ A := by
    intro l hl
    rw [mem_preIn]
    constructor
    · rintro ⟨hl0, h⟩
      rw [hC.onL l hl0 hl] at h
      exact h.1
    · intro h
      refine ⟨SecA.le_fsuL0 T L hl, ?_⟩
      rw [hC.onL l _ hl]
      exact ⟨h, A.one_mem⟩
  have hsurj : ∀ g : L32.Γ, ∃ (l : G) (hl : l ∈ L), ψ (mkO2 L l hl) = g := by
    intro g
    obtain ⟨⟨l, hl⟩, hq⟩ := QuotientGroup.mk_surjective (ψ.symm g)
    exact ⟨l, hl, by rw [mkO2, hq, MulEquiv.apply_symm_apply]⟩
  have hO : ∀ (x : G) (hx : x ∈ L), x ∈ pCoreOf 2 L → x ∈ preIn Ψ (A.prod A) := by
    intro x hx hxO
    rw [hmem x hx, show mkO2 L x hx = 1 from (SecA.mk_eq_one_iff ⟨x, hx⟩).mpr hxO, map_one]
    exact A.one_mem
  refine ⟨lt_of_le_of_ne inf_le_right fun h => ?_, fun J hJ hJL => ?_⟩
  · obtain ⟨g, hg⟩ : ∃ g : L32.Γ, g ∉ A := by
      rcases hA with rfl | rfl
      · exact ⟨_, L32.s2_not_mem_pa⟩
      · exact ⟨_, L32.s1_not_mem_pb⟩
    obtain ⟨l, hl, rfl⟩ := hsurj g
    have : l ∈ preIn Ψ (A.prod A) ⊓ L := by rw [h]; exact hl
    exact hg ((hmem l hl).mp this.1)
  · set A' : Subgroup L32.Γ :=
      (J.subgroupOf L).map (ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    have hAA' : A ≤ A' := by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := hsurj a
      exact ⟨⟨l, hl⟩, hJ.le ⟨(hmem l hl).mpr ha, hl⟩, rfl⟩
    have hlt : A < A' := by
      obtain ⟨j, hjJ, hjn⟩ := IsConcreteLE.exists_of_lt hJ
      have hjL := hJL hjJ
      refine lt_of_le_of_ne hAA' fun h => hjn ⟨(hmem j hjL).mpr ?_, hjL⟩
      rw [h]
      exact ⟨⟨j, hjL⟩, hjJ, rfl⟩
    have htop := L32.eq_top_of_lt hA hlt
    refine le_antisymm hJL fun l hl => ?_
    have hq : ψ (mkO2 L l hl) ∈ A' := htop ▸ Subgroup.mem_top _
    obtain ⟨⟨x, hxL⟩, hxJ, hx⟩ := hq
    have hxl : mkO2 L l hl = mkO2 L x hxL := ψ.injective hx.symm
    have h1 := (mk_eq_mk_iff hl hxL).mp hxl
    have h2 : l * x⁻¹ ∈ J :=
      hJ.le ⟨hO _ (L.mul_mem hl (L.inv_mem hxL)) h1, L.mul_mem hl (L.inv_mem hxL)⟩
    have := J.mul_mem h2 (Subgroup.mem_subgroupOf.mp hxJ)
    simpa using this

namespace Ctx3

variable {H B : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
  {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ}

theorem mem_fsuL0 (c : Ctx3 T L I H B t Ψ α ψ) {z : G} (hz : z ∈ H ⊓ fsuM T L)
    (hzo : Odd (orderOf z)) : z ∈ fsuL0 T L :=
  mem_fsuL0_of_odd c.h37 c.h38 c.h322 c.h1013 c.hyp c.hfaith c.hB (odd_prime_dvd_of_L32 ψ) hz
    hzo

theorem oTwoUpper_le (c : Ctx3 T L I H B t Ψ α ψ) : oTwoUpper (H ⊓ fsuM T L) ≤ fsuL0 T L :=
  (Subgroup.closure_le _).mpr fun _ hz => c.mem_fsuL0 hz.1 hz.2

theorem odd_of_mem (c : Ctx3 T L I H B t Ψ α ψ) {b : G} (hb : b ∈ B) : Odd (orderOf b) :=
  c.hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hb)

theorem le_Y (c : Ctx3 T L I H B t Ψ α ψ) : B ≤ (H ⊓ fsuM T L) ⊓ fsuL0 T L := fun _ hb =>
  ⟨c.hB.1 hb, c.mem_fsuL0 (c.hB.1 hb) (c.odd_of_mem hb)⟩

theorem classify (c : Ctx3 T L I H B t Ψ α ψ) :
    ∃ A : Subgroup L32.Γ, (A = L32.U3 ∨ A = L32.Pa ∨ A = L32.Pb) ∧
      (H ⊓ fsuM T L) ⊓ fsuL0 T L = preIn Ψ (A.prod A) ∧ A.map α.toMonoidHom = A := by
  have hTX : T ≤ H ⊓ fsuM T L := le_inf c.hH.1.1 (SecA.le_fsuM T L)
  have hT0Y : T0 T L ≤ (H ⊓ fsuM T L) ⊓ fsuL0 T L := inf_le_inf_right _ hTX
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L c.ht
  have htY : ∀ y ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L, t⁻¹ * y * t ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L := by
    intro y hy
    have htX := hTX c.ht
    refine ⟨(H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).inv_mem htX) hy.1)
      htX, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp ((fsuM T L).inv_mem htM) y).mp hy.2
    simpa using this
  obtain ⟨A, hA, hY, hαA⟩ := classify_preIn_gen c.hyp.fsu.sylow c.hC hT0Y inf_le_right htY
  refine ⟨A, ?_, hY, hαA⟩
  rcases hA with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    apply not_le_of_isHStar c.h331 c.hyp c.hH
    intro l hl
    have hl0 : l ∈ fsuL0 T L := SecA.le_fsuL0 T L hl
    have : l ∈ preIn Ψ (A.prod A) := mem_preIn.mpr ⟨hl0, by rw [h]; exact ⟨trivial, trivial⟩⟩
    rw [← hY] at this
    exact this.1.1

theorem classify' (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) :
    ∃ A : Subgroup L32.Γ, (A = L32.Pa ∨ A = L32.Pb) ∧
      (H ⊓ fsuM T L) ⊓ fsuL0 T L = preIn Ψ (A.prod A) ∧ A.map α.toMonoidHom = A := by
  obtain ⟨A, hA, hY, hαA⟩ := c.classify
  refine ⟨A, ?_, hY, hαA⟩
  rcases hA with h | h
  · exfalso
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    have hbT0 : b ∈ T0 T L := by
      rw [T0_eq_preIn_gen c.hyp.fsu.sylow c.hC, ← h, ← hY]
      exact c.le_Y hb
    have h2 : IsPGroup 2 (T0 T L) := c.hyp.fsu.sylow.1.to_le inf_le_left
    exact hb1 (Subtype.ext (eq_one_of_mem_of_odd h2 hbT0 (c.odd_of_mem hb)))
  · exact h

theorem eq_two (c : Ctx3 T L I H B t Ψ α ψ) {n : ℕ} (hn : 2 ≤ n) {b₀ : G} (hb₀ : b₀ ∈ B)
    (ho : orderOf b₀ = 2 ^ n - 1) : n = 2 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hb1 : b₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have hB1 : B ≠ ⊥ := fun h => hb1 (by rw [h] at hb₀; exact hb₀)
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hbY := c.le_Y hb₀
  rw [hY] at hbY
  obtain ⟨hbL0, hbA⟩ := mem_preIn.mp hbY
  have h12 : (Ψ ⟨b₀, hbL0⟩) ^ 12 = 1 := by
    obtain ⟨h1, h2⟩ := hbA
    rcases hA with rfl | rfl
    · exact Prod.ext (L32.pa_pow_twelve _ h1) (L32.pa_pow_twelve _ h2)
    · exact Prod.ext (L32.pb_pow_twelve _ h1) (L32.pb_pow_twelve _ h2)
  rw [← map_pow, c.hC.ker] at h12
  have hO : IsPGroup 2 (pCoreOf 2 (fsuL0 T L)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hodd : Odd (orderOf (b₀ ^ 12)) := (c.odd_of_mem hb₀).of_dvd_nat (orderOf_pow_dvd 12)
  have h1 : b₀ ^ 12 = 1 := eq_one_of_mem_of_odd hO (by simpa using h12) hodd
  have hd : 2 ^ n - 1 ∣ 12 := ho ▸ orderOf_dvd_of_pow_eq_one h1
  have hle : 2 ^ n - 1 ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · rfl
  · norm_num at hd

theorem conj_Y (c : Ctx3 T L I H B t Ψ α ψ) {y : G} (hy : y ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L) :
    t⁻¹ * y * t ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L := by
  have htX : t ∈ H ⊓ fsuM T L := ⟨c.hH.1.1 c.ht, SecA.le_fsuM T L c.ht⟩
  refine ⟨(H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).inv_mem htX) hy.1)
    htX, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp ((fsuM T L).inv_mem htX.2) y).mp hy.2
  simpa using this

theorem sup_eq_Y (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) :
    T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L) = (H ⊓ fsuM T L) ⊓ fsuL0 T L := by
  have hTX : T ≤ H ⊓ fsuM T L := le_inf c.hH.1.1 (SecA.le_fsuM T L)
  have hT0Y : T0 T L ≤ (H ⊓ fsuM T L) ⊓ fsuL0 T L := inf_le_inf_right _ hTX
  have hle : T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L) ≤ (H ⊓ fsuM T L) ⊓ fsuL0 T L :=
    sup_le hT0Y (le_inf (CFSG.Quasithin.oTwoUpper_le _) c.oTwoUpper_le)
  have hBO : B ≤ oTwoUpper (H ⊓ fsuM T L) := fun b hb =>
    Subgroup.subset_closure ⟨c.hB.1 hb, c.odd_of_mem hb⟩
  have htX : t ∈ H ⊓ fsuM T L := hTX c.ht
  set f : G →* G := (MulAut.conj t⁻¹).toMonoidHom with hf
  have hfT0 : (T0 T L).map f ≤ T0 T L := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [hf, MulAut.conj_apply] using T.mul_mem (T.mul_mem (T.inv_mem c.ht) hy.1) c.ht
    · have := (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L (T.inv_mem c.ht)) y).mp hy.2
      simpa [hf, MulAut.conj_apply] using this
  have hfO : (oTwoUpper (H ⊓ fsuM T L)).map f ≤ oTwoUpper (H ⊓ fsuM T L) := by
    rw [oTwoUpper, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨hy, hyo⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [hf, MulAut.conj_apply] using (H ⊓ fsuM T L).mul_mem
        ((H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).inv_mem htX) hy) htX
    · rw [hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hyo
  have htY : ∀ y ∈ T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L),
      t⁻¹ * y * t ∈ T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L) := by
    intro y hy
    have h1 : (T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L)).map f ≤ T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup hfT0 hfO
    have := h1 ⟨y, hy, rfl⟩
    simpa [hf, MulAut.conj_apply] using this
  obtain ⟨A'', hA'', hY'', -⟩ :=
    classify_preIn_gen c.hyp.fsu.sylow c.hC le_sup_left (hle.trans inf_le_right) htY
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hAA : A''.prod A'' ≤ A.prod A := by
    rw [← imgIn_preIn c.hC.surj (A''.prod A''), ← imgIn_preIn c.hC.surj (A.prod A), ← hY'', ← hY]
    exact imgIn_mono Ψ hle
  have hA''A : A'' ≤ A := fun a ha => (hAA (show (a, a) ∈ A''.prod A'' from ⟨ha, ha⟩)).1
  have hAeq : A'' = A := by
    rcases hA'' with h | h | h | h
    · exfalso
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
      have hbT0 : b ∈ T0 T L := by
        rw [T0_eq_preIn_gen c.hyp.fsu.sylow c.hC, ← h, ← hY'']
        exact Subgroup.mem_sup_right (hBO hb)
      have h2 : IsPGroup 2 (T0 T L) := c.hyp.fsu.sylow.1.to_le inf_le_left
      exact hb1 (Subtype.ext (eq_one_of_mem_of_odd h2 hbT0 (c.odd_of_mem hb)))
    · rcases hA with rfl | rfl
      · exact h
      · exact absurd (h ▸ hA''A) pa_not_le_pb
    · rcases hA with rfl | rfl
      · exact absurd (h ▸ hA''A) pb_not_le_pa
      · exact h
    · exfalso
      rcases hA with rfl | rfl
      · exact pa_ne_top (top_le_iff.mp (h ▸ hA''A))
      · exact pb_ne_top (top_le_iff.mp (h ▸ hA''A))
  rw [hY'', hY, hAeq]

theorem isMax (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) :
    ∀ K : Subgroup G, IsLi T L K →
      IsMaxSubgroupIn K ((T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L)) ⊓ K) := by
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hYeq := c.sup_eq_Y hB1
  rw [hY] at hYeq
  rw [hYeq]
  intro K hK
  rcases hK with rfl | ⟨t', ht', htn', rfl⟩
  · exact isMax_preIn_inf_L c.hC hA
  · rw [SecA.conjugate_eq_of_not_mem c.h37 c.h38 c.hyp c.ht c.htn ht' htn']
    set f : G ≃* G := MulAut.conj t⁻¹ with hf
    have hLmap : L.map f.toMonoidHom = CFSG.conjugate L t := by
      ext x
      rw [SecA.mem_conjugate_iff]
      constructor
      · rintro ⟨l, hl, rfl⟩
        simpa [hf, MulAut.conj_apply, mul_assoc] using hl
      · intro h
        exact ⟨t * x * t⁻¹, h, by simp [hf, mul_assoc]⟩
    have hYmap : (preIn Ψ (A.prod A)).map f.toMonoidHom = preIn Ψ (A.prod A) := by
      have hle : (preIn Ψ (A.prod A)).map f.toMonoidHom ≤ preIn Ψ (A.prod A) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← hY] at hy ⊢
        simpa [hf, MulAut.conj_apply] using c.conj_Y hy
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [← Nat.card_congr ((preIn Ψ (A.prod A)).equivMapOfInjective _ f.injective).toEquiv]
    rw [← hYmap, ← hLmap, ← Subgroup.map_inf_eq _ _ _ f.injective]
    exact isMaxSubgroupIn_map f (isMax_preIn_inf_L c.hC hA)

end Ctx3

end CFSG.Quasithin.Vol2.Ch10.SecB
