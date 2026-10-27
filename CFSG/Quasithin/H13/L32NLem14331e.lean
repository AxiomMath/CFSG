module

public import CFSG.Quasithin.H13.L32NLem14331d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14330

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem tau_eq_of_mem (B : LinearMap.BilinForm (ZMod 2) W) {α β α' β' : W}
    (hα' : α' = α ∨ α' = β ∨ α' = α + β) (hβ' : β' = α ∨ β' = β ∨ β' = α + β) (hne : α' ≠ β')
    (v : W) : B v α' • β' + B v β' • α' = B v α • β + B v β • α := by
  have key : ∀ (c d : ZMod 2) (x y : W), c • (x + y) + (c + d) • x = c • y + d • x := by
    intro c d x y
    rw [smul_add, add_smul]
    have : c • x + c • x = 0 := ZModModule.add_self _
    calc c • x + c • y + (c • x + d • x) = (c • x + c • x) + c • y + d • x := by abel
      _ = c • y + d • x := by rw [this, zero_add]
  have hBa : B v (α + β) = B v α + B v β := by rw [map_add]
  rcases hα' with h1 | h1 | h1 <;> rcases hβ' with h2 | h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2, hBa, key]
  · rw [h1, h2, add_comm]
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2, hBa, add_comm α β, add_comm (B v α) (B v β), key, add_comm]
  · rw [h1, h2, hBa, add_comm, key]
  · rw [h1, h2, hBa, add_comm, add_comm α β, add_comm (B v α) (B v β), key, add_comm]
  · exact absurd (h1.trans h2.symm) hne

end L14330

namespace L14331

theorem perm_five_centralizer : ∀ z : Equiv.Perm (Fin 5), z ≠ 1 →
    ¬ 24 ∣ (Finset.univ.filter fun w : Equiv.Perm (Fin 5) => w * z = z * w).card := by
  decide +kernel

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem pi_mem_plane {v : G} (hv : v ∈ V)
    (hv1 : v ∉ fsuV1 T V) :
    D.π v = D.π (g⁻¹ * z * g) ∨ D.π v = D.π (z * b) ∨
      D.π v = D.π (g⁻¹ * z * g) + D.π (z * b) := by
  have hzU : z ∈ fsuU T V := V_le_U C.z_V
  have haU : g⁻¹ * z * g ∈ fsuU T V := V_le_U C.a_V
  have hbU : b ∈ fsuU T V := V_le_U C.b_mem
  have hzbU : z * b ∈ fsuU T V := V_le_U (V.mul_mem C.z_V C.b_mem)
  have hz0 : D.π z = 0 := (L128A.HatU.π_eq_zero_iff D hzU).mpr C.z_zU
  have hb : D.π b = D.π (z * b) := by rw [D.π_mul z hzU b hbU, hz0, zero_add]
  have hv1' : v ≠ 1 := fun h => hv1 (h ▸ one_mem _)
  rcases C.V_cases hv hv1' with h | h | h | h | h | h | h <;> subst h
  · exact absurd C.z_mem hv1
  · left; rfl
  · left; rw [D.π_mul z hzU _ haU, hz0, zero_add]
  · right; left; exact hb
  · right; left; rw [D.π_mul b hbU z hzU, hz0, add_zero, hb]
  · right; right; rw [D.π_mul b hbU _ haU, hb, add_comm]
  · right; right
    rw [D.π_mul b hbU _ ((fsuU T V).mul_mem hzU haU), D.π_mul z hzU _ haU, hz0, zero_add, hb,
      add_comm]

theorem rho_comm (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) {t x : G} (htH : t ∈ l32nH T V)
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hx1 : x ≠ 1) (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨t, L14332.l32nH_le_normalizer_fsuU T V htH⟩ * D.ρ ⟨x, hxN⟩ =
      D.ρ ⟨x, hxN⟩ * D.ρ ⟨t, L14332.l32nH_le_normalizer_fsuU T V htH⟩ := by
  obtain ⟨hxN', -, hρ⟩ := C.rho_eq_of_ne D h14325 h1222 h12213 h12810 h12813 hx hx1
  set ρt := D.ρ ⟨t, L14332.l32nH_le_normalizer_fsuU T V htH⟩ with hρt
  have haU : g⁻¹ * z * g ∈ fsuU T V := V_le_U C.a_V
  have hzbU : z * b ∈ fsuU T V := V_le_U (V.mul_mem C.z_V C.b_mem)
  have hmap : ∀ {v : G}, v ∈ V → v ∉ fsuV1 T V → ρt (D.π v) = D.π (g⁻¹ * z * g) ∨
      ρt (D.π v) = D.π (z * b) ∨ ρt (D.π v) = D.π (g⁻¹ * z * g) + D.π (z * b) := by
    intro v hv hv1
    rw [hρt, D.ρ_π _ v (V_le_U hv)]
    refine C.pi_mem_plane D ((Subgroup.mem_normalizer_iff.mp htV v).mp hv)
      fun h => hv1 ?_
    have := (Subgroup.mem_normalizer_iff.mp ((l32nH T V).inv_mem htH) _).mp h
    rwa [show t⁻¹ * (t * v * t⁻¹) * t⁻¹⁻¹ = v by group] at this
  have hα := hmap C.a_V C.a_nmem
  have hβ := hmap (V.mul_mem C.z_V C.b_mem) C.zb_nmem
  have hne : ρt (D.π (g⁻¹ * z * g)) ≠ ρt (D.π (z * b)) := fun h =>
    C.pi_a_ne_pi_zb D h1222 h12213 (ρt.injective h)
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρ, hρ, map_add, map_add, map_smul, map_smul]
  congr 1
  rw [← L128A.HatU.B_rho D ⟨t, L14332.l32nH_le_normalizer_fsuU T V htH⟩ v,
    ← L128A.HatU.B_rho D ⟨t, L14332.l32nH_le_normalizer_fsuU T V htH⟩ v]
  exact L14330.tau_eq_of_mem D.B hα hβ hne _

omit [Finite G] [IsMulCommutative ↥V] C in
theorem card_img_T (hT : quasithinIsSylowTwo T) (hTH : T ≤ l32nH T V)
    (h120 : Nat.card ↥(D.img (l32nH T V)) = 120) :
    Nat.card ↥((T.subgroupOf (l32nH T V)).map (L14332.imgHom D)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (T.subgroupOf (l32nH T V)).map (L14332.imgHom D) with hP
  have hT' : IsPGroup 2 ↥(T.subgroupOf (l32nH T V)) := fun x => by
    obtain ⟨k, hk⟩ := hT.1 ⟨((x : ↥(l32nH T V)) : G), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hP2 : IsPGroup 2 ↥P := hT'.map _
  have hidx : ¬ 2 ∣ P.index := by
    intro h2
    apply hT.2
    have h1 : P.index ∣ (T.subgroupOf (l32nH T V)).index :=
      Subgroup.index_map_dvd _ (L14332.imgHom_surjective D)
    have h2' : (T.subgroupOf (l32nH T V)).index ∣ T.index :=
      Subgroup.relIndex_dvd_index_of_le hTH
    exact (h2.trans h1).trans h2'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hmul := Subgroup.card_mul_index P
  rw [h120, hk] at hmul
  have hk3 : k = 3 := by
    have hodd : ¬ 2 ∣ P.index := hidx
    rcases Nat.lt_or_ge k 4 with hlt | hge
    · interval_cases k
      · exfalso; apply hodd; omega
      · exfalso; apply hodd; omega
      · exfalso; apply hodd; omega
      · rfl
    · exfalso
      have : 2 ^ 4 ∣ 120 := by
        rw [← hmul]
        exact Dvd.dvd.mul_right (pow_dvd_pow 2 hge) _
      norm_num at this
  rw [hk, hk3]
  norm_num

theorem false_of_case_ii (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1) (hii : Case14323ii T V g D) :
    False := by
  obtain ⟨φ⟩ := hii.iso
  have ha := C.conj_mem_zIl he
  have haH : l⁻¹ * e * l ∈ l32nH T V := L14332.conj_zU_le h12813 C.setting C.gP C.gN ha.1
  have haN := L14332.l32nH_le_normalizer_fsuU T V haH
  have ha1 : l⁻¹ * e * l ≠ 1 := fun h => he1 (by
    calc e = l * (l⁻¹ * e * l) * l⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨hmem, hρ1⟩ := C.rho_a_mem D h14325 h1222 h12213 h12810 h12813 he he1 haN
  set w : Equiv.Perm (Fin 5) := φ ⟨D.ρ ⟨l⁻¹ * e * l, haN⟩, hmem⟩ with hw
  have hw1 : w ≠ 1 := fun h => hρ1 (by
    have := φ.injective (h.trans φ.map_one.symm)
    exact congrArg Subtype.val this)
  have hcomm : ∀ {t : G} (htH : t ∈ l32nH T V), t ∈ Subgroup.normalizer (V : Set G) →
      φ (L14332.imgHom D ⟨t, htH⟩) ∈ Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5))) := by
    intro t htH htV
    rw [Subgroup.mem_centralizer_singleton_iff, hw, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (C.rho_comm D h14325 h1222 h12213 h12810 h12813 htH htV ha ha1 haN)
  have hTH : T ≤ l32nH T V := C.setting.v1.2.2
  have h120 : Nat.card ↥(D.img (l32nH T V)) = 120 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hP8 := card_img_T D C.S.hH.sylow hTH h120
  have hPC : ((T.subgroupOf (l32nH T V)).map (L14332.imgHom D)).map
      (φ : ↥(D.img (l32nH T V)) →* Equiv.Perm (Fin 5)) ≤
      Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5))) := by
    rintro _ ⟨p, ⟨t, ht, rfl⟩, rfl⟩
    exact hcomm t.2 (C.S.TV (Subgroup.mem_subgroupOf.mp ht))
  have h8 : 8 ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5)))) := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [Subgroup.card_map_of_injective φ.injective, hP8] at this
  obtain ⟨y, hyL, hy3, hyz, hya⟩ := C.exists_x
  have hyH : y ∈ l32nH T V := C.mem_normalizer_V1 hyz
  have hyC := hcomm hyH (C.L_le hyL)
  have hy1 : φ (L14332.imgHom D ⟨y, hyH⟩) ≠ 1 := by
    intro h
    have h1 : L14332.imgHom D ⟨y, hyH⟩ = 1 := φ.injective (h.trans φ.map_one.symm)
    have h2 := congrArg Subtype.val h1
    rw [L14332.imgHom_apply] at h2
    have h3 := congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ (D.π (g⁻¹ * z * g))) h2
    simp only at h3
    rw [D.ρ_π _ _ (V_le_U C.a_V), hya] at h3
    exact C.pi_a_ne_pi_zb D h1222 h12213 h3.symm
  have hy3' : φ (L14332.imgHom D ⟨y, hyH⟩) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, show (⟨y, hyH⟩ : ↥(l32nH T V)) ^ 3 = 1 from Subtype.ext hy3,
      map_one, map_one]
  have h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5)))) := by
    have := Subgroup.orderOf_dvd_natCard _ hyC
    rwa [orderOf_eq_prime hy3' hy1] at this
  have h24 : 24 ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5)))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
  apply perm_five_centralizer w hw1
  have hcard : Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 5)))) =
      (Finset.univ.filter fun v : Equiv.Perm (Fin 5) => v * w = w * v).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      Subgroup.mem_centralizer_singleton_iff)
  rwa [hcard] at h24

end Ctx

end L14328

end CFSG.Quasithin.H13
