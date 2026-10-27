module

public import Certificates.Certificate7254
public import CFSG.Quasithin.Vol2.Ch12Sec7ModT

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem cert54_ker :
    ∀ B ∈ nm6, (∀ i : Fin 6, permFn B i = i) → B ∈ zs6 :=
  Certificates.certificate7254.1

theorem cert54_one :
    ∀ a ∈ invs6, fVl [a] * f4l [a] * 4 < 1024 :=
  Certificates.certificate7254.2.1

theorem cert54_two :
    ∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a →
      fVl [a, b] * f4l [a, b] * 16 < 1024 :=
  Certificates.certificate7254.2.2.1

theorem cert54_three :
    ∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b →
        fVl [a, b, c] * f4l [a, b, c] * 64 < 1024 :=
  Certificates.certificate7254.2.2.2.1

theorem cert54_rank :
    ∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b → ∀ d ∈ invs6,
        a.comp d = d.comp a → b.comp d = d.comp b → c.comp d = d.comp c → d ∈ span3 a b c :=
  Certificates.certificate7254.2.2.2.2

theorem pn_wV : ∀ x < 64, pn (wV x) = pn x := by decide

theorem oVecL_eq_pn : ∀ d ∈ oVecL, d = pn d ∨ d = wV (pn d) ∨ d = wV (wV (pn d)) := by decide

theorem oVecL_pn_mem : ∀ d ∈ oVecL, pn d ∈ oPts ∧ pn d < 64 := by decide

theorem oPts_idx : ∀ q ∈ oPts, oPts.getD (oPts.idxOf q) 0 = q ∧ oPts.idxOf q < 6 := by decide

theorem oPts_getD_mem : ∀ i : Fin 6, oPts.getD i 0 ∈ oVecL := by decide

theorem permFn_id : ∀ i : Fin 6, permFn B6.id i = i := by decide

theorem permFn_comp {B C : B6} (hB : IsLin B ∨ IsSemi B) (hBv : B.Valid)
    (hC : ∀ c ∈ oVecL, C.app c ∈ oVecL) (i : Fin 6) :
    permFn (B.comp C) i = permFn B (permFn C i) := by
  obtain ⟨d, hddef⟩ : ∃ d, d = C.app (oPts.getD i 0) := ⟨_, rfl⟩
  have hd : d ∈ oVecL := hddef ▸ hC _ (oPts_getD_mem i)
  have e := oVecL_eq_pn d hd
  obtain ⟨hq, hq64⟩ := oVecL_pn_mem d hd
  obtain ⟨hget, hlt⟩ := oPts_idx _ hq
  have h1 : permFn C i = ⟨oPts.idxOf (pn d), hlt⟩ := Fin.ext (by
    show permIdx C i % 6 = _
    rw [permIdx, ← hddef]
    exact Nat.mod_eq_of_lt hlt)
  rw [h1]
  apply Fin.ext
  simp only [permFn, permIdx, B6.app_comp]
  rw [← hddef, hget]
  congr 2
  generalize pn d = p at e hq64 ⊢
  have hw := wV_lt _ hq64
  have k0 := B6.app_lt hBv p
  have k1 := wV_lt _ k0
  have k2 := wV_lt _ k1
  have k3 := wV_lt _ k2
  rcases e with rfl | rfl | rfl
  · rfl
  · rcases hB with hl | hs
    · rw [hl _ hq64, pn_wV _ k0]
    · rw [hs _ hq64, pn_wV _ k1, pn_wV _ k0]
  · rcases hB with hl | hs
    · rw [hl _ hw, hl _ hq64, pn_wV _ k1, pn_wV _ k0]
    · rw [hs _ hw, hs _ hq64, pn_wV _ k3, pn_wV _ k2, pn_wV _ k1, pn_wV _ k0]

variable {G : Type} [Group G] {V K : Subgroup G} [IsMulCommutative ↥V]

open scoped IsMulCommutative

@[expose] noncomputable def piHom (C : Coding ↥V) (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hcode : ∀ g : ↥K, (IsLin (C.cB (conjAct V (Subgroup.inclusion hK g))) ∨
      IsSemi (C.cB (conjAct V (Subgroup.inclusion hK g)))) ∧
      ∀ c ∈ oVecL, (C.cB (conjAct V (Subgroup.inclusion hK g))).app c ∈ oVecL) :
    ↥K →* Equiv.Perm (Fin 6) where
  toFun g :=
    { toFun := permFn (C.cB (conjAct V (Subgroup.inclusion hK g)))
      invFun := permFn (C.cB (conjAct V (Subgroup.inclusion hK g⁻¹)))
      left_inv := fun i => by
        rw [← permFn_comp (hcode g⁻¹).1 (C.cB_valid _) (hcode g).2, ← C.cB_mul, ← map_mul,
          ← map_mul, inv_mul_cancel, map_one, map_one, C.cB_one, permFn_id]
      right_inv := fun i => by
        rw [← permFn_comp (hcode g).1 (C.cB_valid _) (hcode g⁻¹).2, ← C.cB_mul, ← map_mul,
          ← map_mul, mul_inv_cancel, map_one, map_one, C.cB_one, permFn_id] }
  map_one' := Equiv.ext fun i => by
    show permFn (C.cB (conjAct V (Subgroup.inclusion hK 1))) i = i
    rw [map_one, map_one, C.cB_one, permFn_id]
  map_mul' g g' := Equiv.ext fun i => by
    show permFn (C.cB (conjAct V (Subgroup.inclusion hK (g * g')))) i =
      permFn (C.cB (conjAct V (Subgroup.inclusion hK g)))
        (permFn (C.cB (conjAct V (Subgroup.inclusion hK g'))) i)
    rw [map_mul, map_mul, C.cB_mul, permFn_comp (hcode g).1 (C.cB_valid _) (hcode g').2]

end CFSG.Quasithin.H13.S127.Mod
