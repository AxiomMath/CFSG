module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Aa

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4A

variable {W : Type} [CommGroup W]

def fixSub (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    show g (a * b) = a * b
    rw [map_mul, show g a = a from ha, show g b = b from hb]
  inv_mem' := fun {a} ha => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha]

theorem mem_fixSub {g : MulAut W} {w : W} : w ∈ fixSub g ↔ g w = w := Iff.rfl

@[expose] def nMap (g : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => g w * w⁻¹) fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem nMap_apply (g : MulAut W) (w : W) : nMap g w = g w * w⁻¹ := rfl

theorem ker_nMap (g : MulAut W) : (nMap g).ker = fixSub g := by
  ext w
  simp [nMap_apply, mul_inv_eq_one, mem_fixSub]

theorem exists_elation [Finite W] (hWc : Nat.card W = 2 ^ 6) {Γ Ah P : Subgroup (MulAut W)} {z : MulAut W}
    (hG : HatGrp Γ Ah z) (hfpf : ∀ w : W, z w = w → w = 1) (hPΓ : P ≤ Γ) (hP1 : P ≠ ⊥) {V : Subgroup W}
    (hV16 : Nat.card ↥V = 16) (hPV : ∀ p ∈ P, ∀ v ∈ V, p v = v) : ∃ p ∈ P, p ∈ Ah ∧ p ≠ 1 := by
  by_contra hcon
  have hno : ∀ p ∈ P, p ∈ Ah → p = 1 := fun p hp hpA => by
    by_contra hp1
    exact hcon ⟨p, hp, hpA, hp1⟩
  obtain ⟨⟨t, htP⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htA : t ∉ Ah := fun h => ht1' (hno t htP h)
  have hout := hG.outer t (hPΓ htP) htA
  have htz : t * z = z⁻¹ * t := mul_inv_eq_iff_eq_mul.1 hout
  have hz3 := hG.z_cube
  have hinf : V ⊓ V.map z.toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvm⟩ := Subgroup.mem_inf.1 hv
    obtain ⟨u, huV, huv⟩ := Subgroup.mem_map.1 hvm
    have huv' : z u = v := huv
    have h1 : t (z u) = z⁻¹ (t u) := by
      have := congrArg (fun g : MulAut W => g u) htz
      simpa [MulAut.mul_apply] using this
    rw [huv', hPV t htP v hvV, hPV t htP u huV] at h1
    have h2 : z (z u) = u := by
      rw [huv', h1, MulAut.apply_inv_self]
    have h3 : z u = u := by
      have h4 := z_cube_apply hz3 u
      rw [h2] at h4
      exact h4
    have hu1 : u = 1 := hfpf u h3
    rw [Subgroup.mem_bot, ← huv', hu1, map_one]
  have hmap : Nat.card ↥(V.map z.toMonoidHom) = 16 :=
    (Subgroup.card_map_of_injective z.injective).trans hV16
  have hge := card_mul_le_card_sup hinf
  have hle := Subgroup.card_le_card_group (V ⊔ V.map z.toMonoidHom)
  rw [hV16, hmap] at hge
  rw [hWc] at hle
  omega

theorem elation_core [Finite W] (hWc : Nat.card W = 2 ^ 6) (hW2 : ∀ w : W, w * w = 1) {z p : MulAut W}
    (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) (hpz : p * z = z * p) (hp1 : p ≠ 1) {k : ℕ}
    (hpk : p ^ 2 ^ k = 1) {V : Subgroup W} (hV16 : Nat.card ↥V = 16) (hV : ∀ v ∈ V, p v = v) :
    p * p = 1 ∧ V = fixSub p := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hW2 w)
  have hcomm : ∀ x : W, p (z x) = z (p x) := fun x => by
    have := congrArg (fun g : MulAut W => g x) hpz
    simpa [MulAut.mul_apply] using this
  have hzC : ∀ x ∈ fixSub p, z x ∈ fixSub p := fun x hx => by
    rw [mem_fixSub] at hx ⊢
    rw [hcomm, hx]
  have hVC : V ≤ fixSub p := fun v hv => mem_fixSub.2 (hV v hv)
  have hdvd : Nat.card (fixSub p) ∣ 2 ^ 6 := hWc ▸ Subgroup.card_subgroup_dvd_card _
  have hge : 16 ≤ Nat.card (fixSub p) := hV16 ▸ Subgroup.card_le_of_le hVC
  have hmod := card_mod_three hz3 hfpf hzC
  have hne64 : Nat.card (fixSub p) ≠ 64 := by
    intro h
    have htop : fixSub p = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 (by rw [h, hWc]; norm_num)
    apply hp1
    ext w
    have hw : w ∈ fixSub p := htop ▸ Subgroup.mem_top w
    simpa using mem_fixSub.1 hw
  have h16 : Nat.card (fixSub p) = 16 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hi'] at hge hmod hne64 ⊢
    interval_cases i <;> omega
  have hVeq : V = fixSub p := Subgroup.eq_of_le_of_card_ge hVC (by omega)
  have hrange : Nat.card (nMap p).range = 4 := by
    have h1 := Subgroup.card_mul_index (nMap p).ker
    rw [Subgroup.index_ker, ker_nMap, h16, hWc] at h1
    omega
  have hrz : ∀ x ∈ (nMap p).range, z x ∈ (nMap p).range := by
    rintro x ⟨w, rfl⟩
    refine ⟨z w, ?_⟩
    simp only [nMap_apply, map_mul, map_inv, hcomm]
  have hrp : ∀ x ∈ (nMap p).range, p x ∈ (nMap p).range := by
    rintro x ⟨w, rfl⟩
    refine ⟨p w, ?_⟩
    simp only [nMap_apply, map_mul, map_inv]
  have hnot3 : ¬ 3 ∣ 2 ^ k := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hfix := fix_of_stable hz3 hfpf hpz (isPt_iff.2 ⟨hrange, hrz⟩) hrp hnot3 hpk
  refine ⟨?_, hVeq⟩
  ext w
  have h1 := hfix (nMap p w) ⟨w, rfl⟩
  rw [nMap_apply, map_mul, map_inv, hinv (p w), hinv w] at h1
  have h2 : p (p w) = w := mul_right_cancel (h1.trans (mul_comm _ _))
  simpa [MulAut.mul_apply] using h2

end Q4A

end S153Q

end CFSG.Quasithin
