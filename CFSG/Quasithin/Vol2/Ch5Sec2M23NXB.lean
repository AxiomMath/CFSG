module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Norm3Facts
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Zeta

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.M23Norm3 CFSG.M23Heptad CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.L246.C123 (A7)
open CFSG.Quasithin.Asc94 (heptad₀)
open scoped Pointwise

theorem exists_eq_of_injective_of_mem {ι : Fin 7 → Fin 23}
    (hι : Function.Injective ι) (hιH : ∀ i, ι i ∈ heptad₀) {x : Fin 23} (hx : x ∈ heptad₀) :
    ∃ i, ι i = x := by
  classical
  have hsub : Finset.univ.image ι ⊆ heptad₀ := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact hιH i
  have hcard : heptad₀.card ≤ (Finset.univ.image ι).card := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
    exact M23Insp.chk_card.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq] at hx
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
  exact ⟨i, hi⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_Ubar_iff_of_isPermEquiv {M2 : Subgroup G}
    {π : ↥M2 →* Perm (Fin 7)} {ι : Fin 7 → Fin 23}
    {ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)} (hι : Function.Injective ι)
    (hιH : ∀ i, ι i ∈ heptad₀) (hζ : IsPermEquiv M2 π ι ζ) (g : ↥M2) :
    ζ g ∈ πbar.ker ↔ π g = 1 := by
  rw [mem_ker_πbar]
  constructor
  · intro h
    ext i
    have h1 := h (ι i) (hιH i)
    rw [hζ g i] at h1
    exact congrArg Fin.val (hι h1)
  · intro h x hx
    obtain ⟨i, rfl⟩ := exists_eq_of_injective_of_mem hι hιH hx
    rw [hζ g i, h, Perm.one_apply]

theorem centralizer_le_M2_of_mem
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {u : G}
    (hu : u ∈ pCoreOf 2 M2) (hu1 : u ≠ 1) : Subgroup.centralizer ({u} : Set G) ≤ M2 := by
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of hQ hyp hM23 hS
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  obtain ⟨m, hm, hmz⟩ := stmt5_2_12_transitive_of hQ hyp hM23 hS z hzU u hu hz1 hu1
  have hC := centralizer_le_of_setting hQ h5211 hyp hM23 hS hz2 hzT hzU
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : m⁻¹ * g * m ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * g * m * z = m⁻¹ * (g * (m * z * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * z * m⁻¹) * g) * m := by rw [hmz, hg]
      _ = z * (m⁻¹ * g * m) := by group
  have e : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e]
  exact M2.mul_mem (M2.mul_mem hm (hC hg')) (M2.inv_mem hm)

theorem not_nine_dvd_card_centralizer
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {u : G} (hu : u ∈ pCoreOf 2 M2) (hu1 : u ≠ 1) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨π', ρ, -, hker, -, hρ, hU16, -, -, -, hπ'⟩ := exists_rho_of_setting hQ hyp hM23 hS
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  have hCM2 : C ≤ M2 := centralizer_le_M2_of_mem hQ h5211 hyp hM23 hS hu hu1
  set u' : ↥(pCoreOf 2 M2) := ⟨u, hu⟩
  have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have htr : ∀ v : ↥(pCoreOf 2 M2), v ≠ 1 → ∃ g, ρ g u' = v := by
    intro v hv
    obtain ⟨m, hm, hmv⟩ := stmt5_2_12_transitive_of hQ hyp hM23 hS u hu v v.2 hu1
      (fun h => hv (Subtype.ext h))
    refine ⟨π' ⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hρ]
    exact hmv
  have h168 : Nat.card (vecStab ρ u') * 15 = 2520 := by
    rw [card_vecStab_mul ρ hU16 hu'1 htr, CFSG.QuasithinUnique.L246.C123.card_A7]
  have hmapπ : (C.subgroupOf M2).map π ≤
      (vecStab ρ u').map (alternatingGroup (Fin 7)).subtype := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨π' m, ?_, hπ' m⟩
    rw [SetLike.mem_coe, mem_vecStab]
    apply Subtype.ext
    rw [hρ]
    have hmC := Subgroup.mem_subgroupOf.mp hm
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hmC
    calc (m : G) * u * (m : G)⁻¹ = u * m * (m : G)⁻¹ := by rw [hmC]
      _ = u := by group
  have hd1 : Nat.card ((C.subgroupOf M2).map π) ∣ 168 := by
    have h := Subgroup.card_dvd_of_le hmapπ
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at h
    have h' : Nat.card (vecStab ρ u') = 168 := by omega
    rwa [h'] at h
  have hd2 : Nat.card ↥(C ⊓ pCoreOf 2 M2) ∣ 16 :=
    hU16 ▸ Subgroup.card_dvd_of_le inf_le_right
  have h1 := card_map_mul_card_inf hS.ker_eq hCM2
  intro h9
  rw [← h1] at h9
  have h2 : Nat.card ((C.subgroupOf M2).map π) * Nat.card ↥(C ⊓ pCoreOf 2 M2) ∣ 168 * 16 :=
    Nat.mul_dvd_mul hd1 hd2
  have := h9.trans h2
  norm_num at this

@[expose] def yB : ↥M2bar := ⟨yBar, evalN_mem_M2bar _⟩

@[expose] def y1B : ↥M2bar := ⟨y1Bar, evalN_mem_M2bar _⟩

theorem uBar_mem_es : uBar ∈ M23Insp.data.Es := by
  show M23Insp.data.Es.getD 6 1 ∈ M23Insp.data.Es
  rw [List.getD_eq_getElem _ _ (by rw [M23Insp.valid.Es_len]; norm_num)]
  exact List.getElem_mem _

@[expose] noncomputable def uB : ↥M2bar :=
  ⟨uBar, es_mem_M2bar _ uBar_mem_es⟩

theorem uB_mem_Ubar :
    uB ∈ Ubar := (mem_ker_πbar_iff _).mpr uBar_mem_es

theorem πbar_yB :
    πbar yB = c33 := πbar_eq_iff.mpr yBar_facts.1

theorem πbar_y1B :
    πbar y1B = c123 := πbar_eq_iff.mpr yBar_facts.2.1

theorem mem_of_commute_yB_uB
    {m : ↥M2bar} (h1 : m * yB = yB * m) (h2 : m * uB = uB * m) :
    ∃ e ∈ Ubar, e * yB = yB * e ∧ ∃ a : ℕ, m = e * yB ^ a := by
  have hc : πbar m * c33 = c33 * πbar m := by
    have := congrArg πbar h1
    rwa [map_mul, map_mul, πbar_yB] at this
  obtain ⟨a, b, hab⟩ := exists_eq_of_commute_c33
    (Equiv.Perm.mem_alternatingGroup.mp (πbar_mem_alt m)) hc
  set w : ↥M2bar := yB ^ (a : ℕ) * y1B ^ (b : ℕ) with hw
  have hπw : πbar w = πbar m := by
    rw [hw, map_mul, map_pow, map_pow, πbar_yB, πbar_y1B, hab]
  have he : m * w⁻¹ ∈ Ubar := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπw, mul_inv_cancel]
  have hEs := (mem_ker_πbar_iff _).mp he
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hEs
  have hi16 : i < 16 := by rw [← M23Insp.valid.Es_len]; exact hi
  have hget : M23Insp.es.getD i 1 = ((m * w⁻¹ : ↥M2bar) : ↥NativeSporadic.M23) := by
    show M23Insp.data.Es.getD i 1 = _
    rw [List.getD_eq_getElem _ _ hi]
    exact hie
  have hmw : ((m : ↥M2bar) : ↥NativeSporadic.M23) =
      M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) := by
    rw [hget, mul_assoc]
    have : ((w : ↥M2bar) : ↥NativeSporadic.M23) = yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) := rfl
    rw [← this]
    simp
  have h1' : M23Insp.es.getD (⟨i, hi16⟩ : Fin 16) 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * yBar =
      yBar * (M23Insp.es.getD (⟨i, hi16⟩ : Fin 16) 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) := by
    have := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hmw] at this
    exact this
  have h2' : M23Insp.es.getD (⟨i, hi16⟩ : Fin 16) 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * uBar =
      uBar * (M23Insp.es.getD (⟨i, hi16⟩ : Fin 16) 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) := by
    have := congrArg Subtype.val h2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hmw] at this
    exact this
  obtain ⟨hb0, hecomm⟩ := coset_facts ⟨i, hi16⟩ a b h1' h2'
  refine ⟨m * w⁻¹, he, ?_, a, ?_⟩
  · apply Subtype.ext
    show ((m * w⁻¹ : ↥M2bar) : ↥NativeSporadic.M23) * yBar =
      yBar * ((m * w⁻¹ : ↥M2bar) : ↥NativeSporadic.M23)
    rw [← hget]
    exact hecomm
  · rw [hw, hb0]
    simp

@[expose] def rB : ↥M2bar := ⟨rBar, evalN_mem_M2bar _⟩

theorem card_Ubar_commute_yB :
    Nat.card {e : ↥M2bar // e ∈ Ubar ∧ e * yB = yB * e} = 4 := by
  classical
  set P : ↥NativeSporadic.M23 → Prop := fun e => e * yBar = yBar * e
  have e1 : Nat.card {e : ↥M2bar // e ∈ Ubar ∧ e * yB = yB * e} =
      Nat.card {x : ↥NativeSporadic.M23 // x ∈ M23Insp.data.Es ∧ P x} := by
    refine Nat.card_congr
      { toFun := fun e => ⟨(e.1 : ↥NativeSporadic.M23), (mem_ker_πbar_iff _).mp e.2.1,
          congrArg Subtype.val e.2.2⟩
        invFun := fun x => ⟨⟨x.1, es_mem_M2bar _ x.2.1⟩, (mem_ker_πbar_iff _).mpr x.2.1,
          Subtype.ext x.2.2⟩
        left_inv := fun e => rfl
        right_inv := fun x => rfl }
  rw [e1]
  have e2 : Nat.card {x : ↥NativeSporadic.M23 // x ∈ M23Insp.data.Es ∧ P x} =
      (M23Insp.data.Es.filter (fun e => decide (P e))).toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp [List.mem_toFinset]
  rw [e2, List.toFinset_card_of_nodup (M23Insp.valid.Es_nodup.filter _)]
  exact yBar_facts.2.2.2.2.2.2.2.2.2

theorem exists_y_u_of_setting
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ y u r : G, y ∈ M2 ∧ orderOf y = 3 ∧ u ∈ pCoreOf 2 M2 ∧ u ≠ 1 ∧ y * u = u * y ∧
      r * u = u * r ∧ r * y * r⁻¹ = y⁻¹ ∧
      (∀ g : G, g * y = y * g → g * u = u * g →
        ∃ e ∈ pCoreOf 2 M2, e * y = y * e ∧ ∃ a : ℕ, g = e * y ^ a) ∧
      Nat.card ↥(pCoreOf 2 M2 ⊓ Subgroup.centralizer ({y} : Set G)) = 4 := by
  obtain ⟨ι, ζ, hι, hιH, hζ⟩ := exists_permEquiv_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hy1, hy2, hy3, hy4, -, huy, hu1, hru, hry, -⟩ := yBar_facts
  set y' : ↥M2 := ζ.symm yB with hy'
  set u' : ↥M2 := ζ.symm uB with hu'
  set r' : ↥M2 := ζ.symm rB with hr'
  have hmemU : ∀ g : ↥M2, ζ g ∈ Ubar → (g : G) ∈ pCoreOf 2 M2 := by
    intro g hg
    have h1 : π g = 1 := (mem_Ubar_iff_of_isPermEquiv hι hιH hζ g).mp hg
    have h2 : g ∈ π.ker := h1
    rw [hS.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hmemU' : ∀ g : ↥M2, (g : G) ∈ pCoreOf 2 M2 → ζ g ∈ Ubar := by
    intro g hg
    have h2 : g ∈ π.ker := by rw [hS.ker_eq, Subgroup.mem_subgroupOf]; exact hg
    exact (mem_Ubar_iff_of_isPermEquiv hι hιH hζ g).mpr h2
  have huB : ζ u' ∈ Ubar := by
    rw [hu', MulEquiv.apply_symm_apply]
    exact uB_mem_Ubar
  have huU : (u' : G) ∈ pCoreOf 2 M2 := hmemU u' huB
  have hu'1 : (u' : G) ≠ 1 := by
    intro h
    have : u' = 1 := Subtype.ext h
    have h2 : uB = 1 := by rw [← ζ.apply_symm_apply uB, ← hu', this, map_one]
    exact hu1 (congrArg Subtype.val h2)
  have hyB3 : orderOf yB = 3 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf yBar = 3
    exact orderOf_eq_prime hy3 hy4
  have hy'3 : orderOf (y' : G) = 3 := by
    rw [Subgroup.orderOf_coe, hy', MulEquiv.orderOf_eq]
    exact hyB3
  have hcomm' : ∀ a b : ↥M2bar, a * b = b * a → ζ.symm a * ζ.symm b = ζ.symm b * ζ.symm a :=
    fun a b h => by rw [← map_mul, ← map_mul, h]
  have hyuB : yB * uB = uB * yB := Subtype.ext huy.symm
  refine ⟨y', u', r', y'.2, hy'3, huU, hu'1, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (hcomm' _ _ hyuB)
  · exact congrArg Subtype.val (hcomm' _ _ (Subtype.ext hru))
  · have : rB * yB * rB⁻¹ = yB⁻¹ := Subtype.ext hry
    have h2 : r' * y' * r'⁻¹ = y'⁻¹ := by
      rw [hr', hy', ← map_inv, ← map_mul, ← map_inv, ← map_mul, this]
    exact congrArg Subtype.val h2
  · intro g hgy hgu
    have hgM2 : g ∈ M2 := centralizer_le_M2_of_mem hQ h5211 hyp hM23 hS huU hu'1
      (Subgroup.mem_centralizer_singleton_iff.mpr hgu)
    set g' : ↥M2 := ⟨g, hgM2⟩
    have h1 : ζ g' * yB = yB * ζ g' := by
      have : g' * y' = y' * g' := Subtype.ext hgy
      have := congrArg ζ this
      rwa [map_mul, map_mul, hy', MulEquiv.apply_symm_apply] at this
    have h2 : ζ g' * uB = uB * ζ g' := by
      have : g' * u' = u' * g' := Subtype.ext hgu
      have := congrArg ζ this
      rwa [map_mul, map_mul, hu', MulEquiv.apply_symm_apply] at this
    obtain ⟨e, he, hey, a, hga⟩ := mem_of_commute_yB_uB h1 h2
    refine ⟨(ζ.symm e : G), hmemU _ (by rw [MulEquiv.apply_symm_apply]; exact he), ?_, a, ?_⟩
    · exact congrArg Subtype.val (hcomm' _ _ hey)
    · have : g' = ζ.symm e * y' ^ a := by
        rw [hy', ← map_pow, ← map_mul, ← hga, MulEquiv.symm_apply_apply]
      have := congrArg Subtype.val this
      simpa using this
  ·
    rw [← card_Ubar_commute_yB]
    refine Nat.card_congr
      { toFun := fun e => ⟨ζ ⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩, ?_, ?_⟩
        invFun := fun e => ⟨(ζ.symm e.1 : G), Subgroup.mem_inf.mpr ⟨hmemU _ (by
          rw [MulEquiv.apply_symm_apply]
          exact e.2.1), ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact hmemU' _ e.2.1
    · have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp e.2).2
      have : (⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩ : ↥M2) * y' =
          y' * ⟨e, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 (e.2.1)⟩ := Subtype.ext h
      have hζy : ζ y' = yB := by rw [hy', MulEquiv.apply_symm_apply]
      have := congrArg ζ this
      rwa [map_mul, map_mul, hζy] at this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcomm' _ _ e.2.2)
    · intro e
      apply Subtype.ext
      simp
    · intro e
      apply Subtype.ext
      simp

end CFSG.Quasithin.H13
