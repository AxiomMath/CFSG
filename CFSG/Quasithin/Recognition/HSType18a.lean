module

public import CFSG.Quasithin.Recognition.HSType154

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting
open scoped Pointwise

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem L_le_J : C.L ≤ C.J := le_sup_left

theorem I0_le_J : C.I0 ≤ C.J := le_sup_right

theorem L2_le_I0 : C.L2 ≤ C.I0 := Subgroup.map_mono (C.M.pre_mono lamS_le_alt)

theorem i_mem_J : (C.i : G) ∈ C.J := C.I0_le_J C.hiI₀

theorem mem_L2_iff (k : G) : k ∈ C.L2 ↔ k ∈ C.L ∧ k ∈ C.I0 :=
  ⟨fun hk => ⟨C.L2_le_L hk, C.L2_le_I0 hk⟩, fun hk => C.hLI₀ k hk.1 hk.2⟩

theorem card_J : Nat.card C.J = 443520 := by
  rw [Nat.card_congr C.Ψ.toEquiv]
  exact card_M22'

theorem exists_stab0_moving :
    ∃ m ∈ stabilizer M22 (0 : Fin 22), m • (1 : Fin 22) = 3 :=
  exists_mem_stabilizer_smul_eq 0 (by decide) (by decide)

theorem not_mem_normalizer_J
    {c : G} (h1 : ∀ k, k ∈ C.L1 ↔ c * k * c⁻¹ ∈ C.L2)
    (hcL : c ∈ Subgroup.normalizer (C.L : Set G)) :
    c ∉ Subgroup.normalizer (C.J : Set G) := by
  intro hcJ
  have hii : (C.i : G)⁻¹ = C.i := inv_eq_of_mul_eq_one_right C.hi2
  set w := c * C.i * c⁻¹ with hw
  have hwJ : w ∈ C.J := (Subgroup.mem_normalizer_iff.mp hcJ _).mp C.i_mem_J
  have hww : w⁻¹ = w := by
    rw [hw]
    simp only [mul_inv_rev, inv_inv, hii, mul_assoc]
  have hL2 : ∀ k ∈ C.L, (k ∈ C.L2 ↔ w * k * w⁻¹ ∈ C.L) := by
    intro k hk
    have hk' : c⁻¹ * k * c ∈ C.L := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hcL) k).mp hk
      rwa [inv_inv] at this
    have s1 : k ∈ C.L2 ↔ c⁻¹ * k * c ∈ C.L1 := by
      rw [h1 (c⁻¹ * k * c), show c * (c⁻¹ * k * c) * c⁻¹ = k by group]
    rw [s1, ← C.hLi _ hk', Subgroup.mem_normalizer_iff.mp hcL (C.i * (c⁻¹ * k * c) * C.i), hww,
      hw, show c * (C.i * (c⁻¹ * k * c) * C.i) * c⁻¹ = c * C.i * c⁻¹ * k * (c * C.i * c⁻¹) by
        group]
  set b : Fin 22 := (C.Ψ ⟨w, hwJ⟩)⁻¹ • (0 : Fin 22) with hb
  have hstab : ∀ y : ↥C.J, (y : G) ∈ C.L → ((y : G) ∈ C.L2 ↔ C.Ψ y • b = b) := by
    intro y hy
    rw [hL2 _ hy]
    have hwy : w * (y : G) * w⁻¹ ∈ C.J := C.J.mul_mem (C.J.mul_mem hwJ y.2) (C.J.inv_mem hwJ)
    have e : (⟨w * (y : G) * w⁻¹, hwy⟩ : ↥C.J) = ⟨w, hwJ⟩ * y * ⟨w, hwJ⟩⁻¹ := rfl
    rw [show w * (y : G) * w⁻¹ ∈ C.L ↔ C.Ψ ⟨w * (y : G) * w⁻¹, hwy⟩ ∈ stabilizer M22 (0 : Fin 22)
      from C.hΨL ⟨_, hwy⟩, e, map_mul, map_mul, map_inv, mem_stabilizer_iff, mul_smul, mul_smul,
      hb]
    constructor
    · intro h0
      have := congrArg ((C.Ψ ⟨w, hwJ⟩)⁻¹ • ·) h0
      simp only [inv_smul_smul] at this
      exact this
    · intro h0
      rw [h0, smul_inv_smul]
  have hb0 : b ≠ 0 := by
    intro hb0
    obtain ⟨m, hm0, hm1⟩ := exists_stab0_moving
    obtain ⟨y, rfl⟩ := C.Ψ.surjective m
    have hyL : (y : G) ∈ C.L := (C.hΨL y).mpr hm0
    have hyL2 : (y : G) ∈ C.L2 := (hstab y hyL).mpr (by rw [hb0]; exact hm0)
    have hyH := (C.hΨI y).mp ((C.mem_L2_iff _).mp hyL2).2
    have := (mem_m22HexStab_iff.mp hyH) 1
    rw [← smul_m22_def, hm1] at this
    exact absurd (this.mpr (by decide)) (by decide)
  obtain ⟨x, hxH, hx0, hxb⟩ : ∃ x : Fin 22, x ∈ m22HexadF ∧ x ≠ 0 ∧ x ≠ b := by
    by_cases hb1 : b = 1
    · exact ⟨2, by decide, by decide, by rw [hb1]; decide⟩
    · exact ⟨1, by decide, by decide, Ne.symm hb1⟩
  obtain ⟨y, hyH, hy0, hyb⟩ : ∃ y : Fin 22, y ∉ m22HexadF ∧ y ≠ 0 ∧ y ≠ b := by
    by_cases hb3 : b = 3
    · exact ⟨4, by decide, by decide, by rw [hb3]; decide⟩
    · exact ⟨3, by decide, by decide, Ne.symm hb3⟩
  obtain ⟨m, hm0, hmb, hmx⟩ := exists_smul_eq_triple (Ne.symm hb0) (Ne.symm hx0) (Ne.symm hxb)
    (Ne.symm hb0) (Ne.symm hy0) (Ne.symm hyb)
  obtain ⟨u, rfl⟩ := C.Ψ.surjective m
  have huL : (u : G) ∈ C.L := (C.hΨL u).mpr hm0
  have huL2 : (u : G) ∈ C.L2 := (hstab u huL).mpr hmb
  have huH := (C.hΨI u).mp ((C.mem_L2_iff _).mp huL2).2
  have := (mem_m22HexStab_iff.mp huH) x
  rw [← smul_m22_def, hmx] at this
  exact hyH (this.mpr hxH)

theorem mem_J_of_mem_normalizer
    {c : G} (hcN : c ∈ Subgroup.normalizer (C.M.V2 : Set G)) (hcNN : c ∉ C.M.NN)
    (hcL : c ∈ Subgroup.normalizer (C.L : Set G)) (hcJ : c ∉ Subgroup.normalizer (C.J : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (C.J : Set G)) : n ∈ C.J := by
  obtain ⟨-, -, -, -, ⟨-, -, hc22, -, -, -, -⟩, -⟩ := m22_point_hexad_actions
  set K := C.L.map (MulAut.conj n).toMonoidHom with hK
  have hKJ : K ≤ C.J := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn k).mp (C.L_le_J hk)
  set K' : Subgroup M22 := (K.subgroupOf C.J).map C.Ψ.toMonoidHom with hK'
  have hcardK : Nat.card K = 20160 := by
    rw [hK, Subgroup.card_map_of_injective (MulAut.conj n).injective, C.card_L]
  have hidx : K'.index = 22 := by
    rw [hK', Subgroup.index_map_of_bijective C.Ψ.bijective]
    have h1 := (K.subgroupOf C.J).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv, hcardK, C.card_J] at h1
    omega
  obtain ⟨a, ha⟩ := hc22 K' hidx
  obtain ⟨m₀, hm₀, -⟩ := exists_smul_eq_pair (a := (0 : Fin 22)) (b := 1) (c := a)
    (d := if a = 1 then 2 else 1) (by decide) (by split_ifs with h <;> simp [h])
  obtain ⟨j, rfl⟩ := C.Ψ.surjective m₀
  have hKj : ∀ y : ↥C.J, (y : G) ∈ K ↔ (j : G)⁻¹ * y * j ∈ C.L := by
    intro y
    have hyJ : (j : G)⁻¹ * y * j ∈ C.J := C.J.mul_mem (C.J.mul_mem (C.J.inv_mem j.2) y.2) j.2
    have e : (⟨(j : G)⁻¹ * y * j, hyJ⟩ : ↥C.J) = j⁻¹ * y * j := rfl
    have h2 : (j : G)⁻¹ * y * j ∈ C.L ↔ C.Ψ ⟨_, hyJ⟩ ∈ stabilizer M22 (0 : Fin 22) :=
      C.hΨL ⟨_, hyJ⟩
    rw [h2, e, map_mul, map_mul, map_inv, mem_stabilizer_iff, mul_smul, mul_smul, hm₀]
    have hmem : (y : G) ∈ K ↔ C.Ψ y ∈ K' := by
      rw [hK', Subgroup.mem_map]
      constructor
      · intro hy
        exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      · rintro ⟨y', hy', hyy'⟩
        rw [C.Ψ.injective hyy'] at hy'
        exact Subgroup.mem_subgroupOf.mp hy'
    rw [hmem, ha, mem_stabilizer_iff]
    constructor
    · intro h0
      rw [h0, ← hm₀, inv_smul_smul]
    · intro h0
      have := congrArg (C.Ψ j • ·) h0
      simp only [smul_inv_smul] at this
      rw [hm₀] at this
      exact this
  have hjn : (j : G)⁻¹ * n ∈ Subgroup.normalizer (C.L : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have hnk : n * k * n⁻¹ ∈ K := ⟨k, hk, rfl⟩
    have := (hKj ⟨_, hKJ hnk⟩).mp hnk
    rwa [show (j : G)⁻¹ * (n * k * n⁻¹) * j = (j : G)⁻¹ * n * k * ((j : G)⁻¹ * n)⁻¹ by group]
      at this
  rcases C.normalizer_L_cases hcN hcNN hcL hjn with h | h
  · rw [show n = (j : G) * ((j : G)⁻¹ * n) by group]
    exact C.J.mul_mem j.2 (C.L_le_J h)
  · exfalso
    apply hcJ
    have hjJ : (j : G) ∈ Subgroup.normalizer (C.J : Set G) := Subgroup.le_normalizer j.2
    rw [show c = ((j : G)⁻¹ * n * c⁻¹)⁻¹ * ((j : G)⁻¹ * n) by group]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem
      (Subgroup.le_normalizer (C.L_le_J h))) ((Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem hjJ) hn)

theorem m22_eq_of_le
    {W X : Subgroup M22} (hXW : X ≤ W) (hX : X.index = 22 ∨ X.index = 77) :
    W = X ∨ W = ⊤ := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, -, hlow⟩, -⟩ := m22_point_hexad_actions
  have hdvd : W.index ∣ X.index := Subgroup.index_dvd_of_le hXW
  by_cases hWt : W = ⊤
  · exact Or.inr hWt
  have hW := hlow W hWt
  rcases hX with h | h <;> rw [h] at hdvd
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases hW (by omega) with h' | h'
    · left
      refine (Subgroup.eq_of_le_of_card_ge hXW ?_).symm
      have e1 := X.card_mul_index
      have e2 := W.card_mul_index
      rw [h] at e1
      rw [h'] at e2
      omega
    · omega
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases hW (by omega) with h' | h'
    · rw [h'] at hdvd
      norm_num at hdvd
    · left
      refine (Subgroup.eq_of_le_of_card_ge hXW ?_).symm
      have e1 := X.card_mul_index
      have e2 := W.card_mul_index
      rw [h] at e1
      rw [h'] at e2
      omega

theorem map_mono_iff (K : Subgroup G) (y : ↥C.J) :
    C.Ψ y ∈ (K.subgroupOf C.J).map C.Ψ.toMonoidHom ↔ (y : G) ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y', hy', hyy'⟩
    rw [C.Ψ.injective hyy'] at hy'
    exact Subgroup.mem_subgroupOf.mp hy'
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem index_stab0 :
    (stabilizer M22 (0 : Fin 22)).index = 22 := by
  have h1 := (stabilizer M22 (0 : Fin 22)).card_mul_index
  rw [card_stabilizer_point, card_M22'] at h1
  omega

theorem eq_J_of_L_le
    {K : Subgroup G} (hLK : C.L ≤ K) (hKJ : K ≤ C.J) : K = C.L ∨ K = C.J := by
  have hle : stabilizer M22 (0 : Fin 22) ≤ (K.subgroupOf C.J).map C.Ψ.toMonoidHom := by
    intro m hm
    obtain ⟨y, rfl⟩ := C.Ψ.surjective m
    exact (C.map_mono_iff K y).mpr (hLK ((C.hΨL y).mpr hm))
  rcases m22_eq_of_le hle (Or.inl index_stab0) with h | h
  · left
    refine le_antisymm (fun k hk => ?_) hLK
    have hkJ := hKJ hk
    have := (C.map_mono_iff K ⟨k, hkJ⟩).mpr hk
    rw [h] at this
    exact (C.hΨL ⟨k, hkJ⟩).mpr this
  · right
    refine le_antisymm hKJ (fun k hk => ?_)
    have := (C.map_mono_iff K ⟨k, hk⟩).mp (by rw [h]; exact Subgroup.mem_top _)
    exact this

theorem index_hexStab (hcard : Nat.card C.I0 = 5760) :
    (m22HexStab).index = 77 := by
  have hJ : Nat.card ↥((C.I0.subgroupOf C.J).map C.Ψ.toMonoidHom) = 5760 := by
    rw [Subgroup.card_map_of_injective C.Ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.I0_le_J).toEquiv, hcard]
  have heq : (C.I0.subgroupOf C.J).map C.Ψ.toMonoidHom = m22HexStab := by
    ext m
    obtain ⟨y, rfl⟩ := C.Ψ.surjective m
    rw [C.map_mono_iff C.I0 y]
    exact C.hΨI y
  rw [heq] at hJ
  have h1 := (m22HexStab).card_mul_index
  rw [hJ, card_M22'] at h1
  omega

theorem card_I0 : Nat.card C.I0 = 5760 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj C.g).injective,
    C.M.card_pre C.h C.hsmemH C.hsnotK C.hss C.hg₀, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem eq_J_of_I0_le
    {K : Subgroup G} (hIK : C.I0 ≤ K) (hKJ : K ≤ C.J) : K = C.I0 ∨ K = C.J := by
  have hle : m22HexStab ≤ (K.subgroupOf C.J).map C.Ψ.toMonoidHom := by
    intro m hm
    obtain ⟨y, rfl⟩ := C.Ψ.surjective m
    exact (C.map_mono_iff K y).mpr (hIK ((C.hΨI y).mpr hm))
  rcases m22_eq_of_le hle (Or.inr (C.index_hexStab C.card_I0)) with h | h
  · left
    refine le_antisymm (fun k hk => ?_) hIK
    have hkJ := hKJ hk
    have := (C.map_mono_iff K ⟨k, hkJ⟩).mpr hk
    rw [h] at this
    exact (C.hΨI ⟨k, hkJ⟩).mpr this
  · right
    refine le_antisymm hKJ (fun k hk => ?_)
    exact (C.map_mono_iff K ⟨k, hk⟩).mp (by rw [h]; exact Subgroup.mem_top _)

theorem mem_hexStab_of_normalizes
    {m : M22}
    (hm : ∀ e ∈ m22HexStab, m⁻¹ * e * m ∈ m22HexStab) : m ∈ m22HexStab := by
  classical
  rw [mem_m22HexStab_iff]
  set σ : Equiv.Perm (Fin 22) := (m : Equiv.Perm (Fin 22)) with hσ
  have hh : hexad0 = m22HexadF := rfl
  have hconj : ∀ e ∈ m22HexStab, ∀ p ∈ m22HexadF,
      σ⁻¹ ((e : Equiv.Perm (Fin 22)) (σ p)) ∈ m22HexadF := by
    intro e he p hp
    have h1 := mem_m22HexStab_iff.mp (hm e he) p
    have e1 : ((m⁻¹ * e * m : M22) : Equiv.Perm (Fin 22)) p =
        σ⁻¹ ((e : Equiv.Perm (Fin 22)) (σ p)) := rfl
    rw [e1] at h1
    exact h1.mpr hp
  have hstab : ∀ e : ↥(stabilizer M22 hexad0), (e : M22) ∈ m22HexStab := by
    intro e
    refine mem_m22HexStab_iff.mpr fun p => ?_
    have he : (e : M22) • hexad0 = hexad0 := e.2
    rw [← hh]
    constructor
    · intro hp
      have hp' : (e : M22) • p ∈ (e : M22) • hexad0 := by rw [he]; exact hp
      exact (Finset.smul_mem_smul_finset_iff (e : M22)).mp hp'
    · intro hp
      have := Finset.smul_mem_smul_finset (a := (e : M22)) hp
      rw [he] at this
      exact this
  have hin : ∀ p ∈ m22HexadF, σ p ∈ m22HexadF := by
    intro p hp
    by_contra hq
    have hall : ∀ y : Fin 22, y ∉ m22HexadF → σ⁻¹ y ∈ m22HexadF := by
      intro y hy
      obtain ⟨e, he⟩ := (exists_stabilizer_apply_eq_iff hexad0_mem (σ p) y).mpr
        (iff_of_false (by rwa [hh]) (by rwa [hh]))
      have := hconj e.1 (hstab e) p hp
      rwa [he] at this
    have hinj : Function.Injective (fun y : {y : Fin 22 // y ∉ m22HexadF} =>
        (⟨σ⁻¹ y, hall y y.2⟩ : {x : Fin 22 // x ∈ m22HexadF})) := by
      intro a b hab
      exact Subtype.ext (σ⁻¹.injective (congrArg Subtype.val hab))
    have hc := Fintype.card_le_of_injective _ hinj
    have h16 : Fintype.card {y : Fin 22 // y ∉ m22HexadF} = 16 := by decide
    have h6 : Fintype.card {x : Fin 22 // x ∈ m22HexadF} = 6 := by decide
    omega
  intro p
  refine ⟨fun hp => ?_, hin p⟩
  by_contra hp'
  have hsurj : Function.Surjective (fun x : {x : Fin 22 // x ∈ m22HexadF} =>
      (⟨σ x, hin x x.2⟩ : {x : Fin 22 // x ∈ m22HexadF})) :=
    Finite.injective_iff_surjective.mp fun a b hab =>
      Subtype.ext (σ.injective (congrArg Subtype.val hab))
  obtain ⟨x, hx⟩ := hsurj ⟨σ p, hp⟩
  have := σ.injective (congrArg Subtype.val hx)
  exact hp' (this ▸ x.2)

theorem mem_hsNB_of_normalizes_pre {m : G}
    (hmP : ∀ x ∈ C.M.pre (alternatingGroup (Fin 6)),
      m * x * m⁻¹ ∈ C.M.pre (alternatingGroup (Fin 6)))
    (hmP' : ∀ x ∈ C.M.pre (alternatingGroup (Fin 6)),
      m⁻¹ * x * m ∈ C.M.pre (alternatingGroup (Fin 6))) :
    m ∈ hsNB C.z C.s := by
  classical
  have hBP : hsB C.z C.s ≤ C.M.pre (alternatingGroup (Fin 6)) := C.M.hsB_le_pre _
  have hPN : C.M.pre (alternatingGroup (Fin 6)) ≤ hsNB C.z C.s := C.M.pre_le_hsNB _
  set Bm := (hsB C.z C.s).map (MulAut.conj m).toMonoidHom with hBm
  have hBmP : Bm ≤ C.M.pre (alternatingGroup (Fin 6)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hmP b (hBP hb)
  set X : Subgroup (Equiv.Perm (Fin 6)) := (Bm.subgroupOf (hsNB C.z C.s)).map C.M.π with hX
  have hXA : X ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨y, hy, rfl⟩
    exact C.M.π_mem_of_mem_pre (hBmP (Subgroup.mem_subgroupOf.mp hy)) y.2
  have hXn : (X.subgroupOf (alternatingGroup (Fin 6))).Normal := by
    refine ⟨fun x hx σ => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨p, hp⟩ := C.M.π_surj σ
    have hpP : (p : G) ∈ C.M.pre (alternatingGroup (Fin 6)) :=
      C.M.mem_pre.mpr ⟨p.2, show C.M.π p ∈ alternatingGroup (Fin 6) by rw [hp]; exact σ.2⟩
    have hqN : m⁻¹ * p * m ∈ hsNB C.z C.s := hPN (hmP' _ hpP)
    have hqb : (m⁻¹ * p * m) * b * (m⁻¹ * p * m)⁻¹ ∈ hsB C.z C.s :=
      (Subgroup.mem_normalizer_iff.mp hqN b).mp hb
    refine ⟨p * y * p⁻¹, Subgroup.mem_subgroupOf.mpr ⟨_, hqb, ?_⟩, ?_⟩
    · show m * ((m⁻¹ * p * m) * b * (m⁻¹ * p * m)⁻¹) * m⁻¹ = (p : G) * y * (p : G)⁻¹
      rw [← hby]
      show m * ((m⁻¹ * p * m) * b * (m⁻¹ * p * m)⁻¹) * m⁻¹ = (p : G) * (m * b * m⁻¹) * (p : G)⁻¹
      group
    · rw [map_mul, map_mul, map_inv, hp, hyx]
      rfl
  rcases @alternatingGroup.normal_subgroup_eq_bot_or_eq_top (Fin 6) _ _ (by simp) _ hXn with h | h
  · refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have hmb : m * b * m⁻¹ ∈ hsNB C.z C.s := hPN (hBmP ⟨b, hb, rfl⟩)
    have hx : C.M.π ⟨m * b * m⁻¹, hmb⟩ ∈ X :=
      ⟨⟨m * b * m⁻¹, hmb⟩, Subgroup.mem_subgroupOf.mpr ⟨b, hb, rfl⟩, rfl⟩
    have hx' : (⟨C.M.π ⟨m * b * m⁻¹, hmb⟩, hXA hx⟩ : ↥(alternatingGroup (Fin 6))) ∈
        X.subgroupOf (alternatingGroup (Fin 6)) := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (C.M.ker _).mp (congrArg Subtype.val hx')
  · exfalso
    have hle : alternatingGroup (Fin 6) ≤ X := fun σ hσ => by
      have : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 6))) ∈ X.subgroupOf (alternatingGroup (Fin 6)) :=
        by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card X ∣ Nat.card ↥(Bm.subgroupOf (hsNB C.z C.s)) :=
      Subgroup.card_map_dvd _ C.M.π
    have h3 : Nat.card ↥(Bm.subgroupOf (hsNB C.z C.s)) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBmP.trans hPN)).toEquiv, hBm,
        Subgroup.card_map_of_injective (MulAut.conj m).injective,
        C.h.card_hsB C.hsmemH C.hsnotK C.hss]
    rw [h3] at h2
    have h4 := Nat.le_of_dvd (by norm_num) h2
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have : Nat.factorial 6 / 2 = 360 := by decide
    omega

theorem exists_d :
    ∃ d ∈ Subgroup.normalizer (C.I0 : Set G), d ∉ C.J ∧
      ∀ n ∈ Subgroup.normalizer (C.I0 : Set G), n ∈ C.I0 ∨ n * d⁻¹ ∈ C.I0 := by
  obtain ⟨n₀, hn₀⟩ := C.M.π_surj (Equiv.swap 0 1)
  have hpre : ∀ x ∈ C.M.pre (alternatingGroup (Fin 6)),
      (n₀ : G) * x * (n₀ : G)⁻¹ ∈ C.M.pre (alternatingGroup (Fin 6)) := by
    intro x hx
    obtain ⟨hxN, hxπ⟩ := C.M.mem_pre.mp hx
    have hm : (n₀ : G) * x * (n₀ : G)⁻¹ ∈ hsNB C.z C.s :=
      (hsNB C.z C.s).mul_mem ((hsNB C.z C.s).mul_mem n₀.2 hxN) ((hsNB C.z C.s).inv_mem n₀.2)
    refine C.M.mem_pre.mpr ⟨hm, ?_⟩
    have e : (⟨(n₀ : G) * x * (n₀ : G)⁻¹, hm⟩ : ↥(hsNB C.z C.s)) = n₀ * ⟨x, hxN⟩ * n₀⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ hxπ _
  set d := C.g * n₀ * C.g⁻¹ with hd
  have hdI : ∀ y ∈ C.I0, d * y * d⁻¹ ∈ C.I0 := by
    intro y hy
    rw [mem_map_conj_iff] at hy ⊢
    have := hpre _ hy
    rwa [hd, show C.g⁻¹ * (C.g * n₀ * C.g⁻¹ * y * (C.g * n₀ * C.g⁻¹)⁻¹) * C.g =
      (n₀ : G) * (C.g⁻¹ * y * C.g) * (n₀ : G)⁻¹ by group]
  have hdN : d ∈ Subgroup.normalizer (C.I0 : Set G) := Subgroup.mem_normalizer_fintype hdI
  refine ⟨d, hdN, fun hdJ => ?_, fun n hn => ?_⟩
  swap
  ·
    set m := C.g⁻¹ * n * C.g with hm
    have hconj : ∀ k : G, k ∈ Subgroup.normalizer (C.I0 : Set G) →
        ∀ x ∈ C.M.pre (alternatingGroup (Fin 6)),
          C.g⁻¹ * k * C.g * x * (C.g⁻¹ * k * C.g)⁻¹ ∈ C.M.pre (alternatingGroup (Fin 6)) := by
      intro k hk x hx
      have hxI : C.g * x * C.g⁻¹ ∈ C.I0 := by
        rw [mem_map_conj_iff, show C.g⁻¹ * (C.g * x * C.g⁻¹) * C.g = x by group]
        exact hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hk _).mp hxI
      rw [mem_map_conj_iff] at h1
      rwa [show C.g⁻¹ * (k * (C.g * x * C.g⁻¹) * k⁻¹) * C.g =
        C.g⁻¹ * k * C.g * x * (C.g⁻¹ * k * C.g)⁻¹ by group] at h1
    have hmN : m ∈ hsNB C.z C.s := by
      refine C.mem_hsNB_of_normalizes_pre (hconj n hn) fun x hx => ?_
      have := hconj n⁻¹ ((Subgroup.normalizer _).inv_mem hn) x hx
      rwa [show C.g⁻¹ * n⁻¹ * C.g * x * (C.g⁻¹ * n⁻¹ * C.g)⁻¹ = m⁻¹ * x * m by rw [hm]; group]
        at this
    by_cases hπ : C.M.π ⟨m, hmN⟩ ∈ alternatingGroup (Fin 6)
    · left
      rw [mem_map_conj_iff]
      exact C.M.mem_pre.mpr ⟨hmN, hπ⟩
    · right
      have hmn : m * (n₀ : G)⁻¹ ∈ hsNB C.z C.s :=
        (hsNB C.z C.s).mul_mem hmN ((hsNB C.z C.s).inv_mem n₀.2)
      rw [mem_map_conj_iff, show C.g⁻¹ * (n * d⁻¹) * C.g = m * (n₀ : G)⁻¹ by rw [hm, hd]; group]
      refine C.M.mem_pre.mpr ⟨hmn, ?_⟩
      have e : (⟨m * (n₀ : G)⁻¹, hmn⟩ : ↥(hsNB C.z C.s)) = ⟨m, hmN⟩ * n₀⁻¹ := rfl
      rw [e, map_mul, map_inv, hn₀, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv,
        Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1)]
      rw [Equiv.Perm.mem_alternatingGroup] at hπ
      rcases Int.units_eq_one_or (Equiv.Perm.sign (C.M.π ⟨m, hmN⟩)) with h1 | h1
      · exact absurd h1 hπ
      · rw [h1]
        decide
  have hnorm : ∀ e ∈ m22HexStab, (C.Ψ ⟨d, hdJ⟩)⁻¹ * e * C.Ψ ⟨d, hdJ⟩ ∈ m22HexStab := by
    intro e he
    obtain ⟨y, rfl⟩ := C.Ψ.surjective e
    have hyI := (C.hΨI y).mpr he
    have hyI' : d⁻¹ * y * d ∈ C.I0 := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hdN) y).mp hyI
      rwa [inv_inv] at this
    have hyJ : d⁻¹ * y * d ∈ C.J := C.I0_le_J hyI'
    have e1 : (⟨d⁻¹ * y * d, hyJ⟩ : ↥C.J) = (⟨d, hdJ⟩ : ↥C.J)⁻¹ * y * ⟨d, hdJ⟩ := rfl
    have := (C.hΨI ⟨_, hyJ⟩).mp hyI'
    rwa [e1, map_mul, map_mul, map_inv] at this
  have hdI0 : d ∈ C.I0 := (C.hΨI ⟨d, hdJ⟩).mpr (mem_hexStab_of_normalizes hnorm)
  rw [mem_map_conj_iff, hd, show C.g⁻¹ * (C.g * n₀ * C.g⁻¹) * C.g = (n₀ : G) by group] at hdI0
  have h1 := C.M.π_mem_of_mem_pre hdI0 n₀.2
  rw [show (⟨(n₀ : G), n₀.2⟩ : ↥(hsNB C.z C.s)) = n₀ from rfl, hn₀,
    Equiv.Perm.mem_alternatingGroup] at h1
  exact absurd h1 (by decide)

theorem eq_one_of_forall_conj_mem {c : G}
    (hcJ : c ∉ Subgroup.normalizer (C.J : Set G)) {x : G} (hx : ∀ y : G, y * x * y⁻¹ ∈ C.J) :
    x = 1 := by
  have : IsSimpleGroup M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hsimple : IsSimpleGroup ↥C.J := C.Ψ.isSimpleGroup
  have hxN : x ∈ C.J.normalCore := hx
  have hNJ : C.J.normalCore ≤ C.J := Subgroup.normalCore_le C.J
  have hnorm : (C.J.normalCore.subgroupOf C.J).Normal := Subgroup.normal_subgroupOf
  rcases hnorm.eq_bot_or_eq_top with h | h
  · have hx' : (⟨x, hNJ hxN⟩ : ↥C.J) ∈ C.J.normalCore.subgroupOf C.J :=
      Subgroup.mem_subgroupOf.mpr hxN
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · exfalso
    apply hcJ
    have hJN : C.J ≤ C.J.normalCore := by
      intro y hy
      have : (⟨y, hy⟩ : ↥C.J) ∈ C.J.normalCore.subgroupOf C.J := by
        rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h2 : ∀ b : G, b * y * b⁻¹ ∈ C.J := hJN hy
      exact h2 c
    · intro hy
      have h2 : ∀ b : G, b * (c * y * c⁻¹) * b⁻¹ ∈ C.J := hJN hy
      have := h2 c⁻¹
      rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at this

end HSCtx

end CFSG.Quasithin.HSType
