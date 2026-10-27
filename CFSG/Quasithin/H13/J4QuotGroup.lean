module

public import CFSG.Quasithin.H13.J4SecondLocal
public import Certificates.Data.CFSGNative.H13.J4Local
public meta import Certificates.Data.CFSGNative.H13.J4Local
public meta import Certificates.Data.CFSGNative.H13.J4Data
public meta import CFSG.Quasithin.H13.J4Image
public import CFSG.Quasithin.H13.J4QuotGroupInputs
public import Certificates.Certificate7016
public import Certificates.Certificate7013
public import Certificates.Certificate7012
public import Certificates.Certificate7014
public import Certificates.Certificate7015
public import Certificates.Certificate7018

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Quasithin.H13.J4.Native

theorem map_wordProd' {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : ℕ → G)
    (w : List ℤ) : f (wordProd gs w) = wordProd (fun i => f (gs i)) w := by
  unfold wordProd
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply]
  split_ifs <;> simp

abbrev QW : Type := W ⧸ P.subgroupOf W

@[expose] def Uq : QW := QuotientGroup.mk ⟨u, u_mem_W⟩

@[expose] def Vq : QW := QuotientGroup.mk ⟨v, v_mem_W⟩

theorem ker_rho12_eq :
    rho12.ker = P.subgroupOf W :=
  ker_rho12.trans ker_rho_eq_and_card_range.1

@[expose] def qEquiv :
    QW ≃* rho12.range :=
  (QuotientGroup.quotientMulEquivOfEq ker_rho12_eq.symm).trans
    (QuotientGroup.quotientKerEquivRange rho12)

@[expose] def qHom :
    QW →* GL (Fin 12) (ZMod 2) := rho12.range.subtype.comp qEquiv.toMonoidHom

theorem qHom_injective :
    Function.Injective qHom :=
  Subtype.val_injective.comp qEquiv.injective

theorem qHom_Uq :
    qHom Uq = U12 := rfl

theorem qHom_Vq :
    qHom Vq = V12 := rfl

theorem card_QW :
    Nat.card QW = 2661120 := by
  rw [Nat.card_congr qEquiv.toEquiv, card_range_rho12, ker_rho_eq_and_card_range.2]

@[expose] def uvQ
    (i : ℕ) :
    QW := if i = 0 then Uq else if i = 1 then Vq else 1

theorem qHom_uvQ
    (i : ℕ) :
    qHom (uvQ i) = uvGen12 i := by
  unfold uvQ uvGen12
  split_ifs <;> simp [qHom_Uq, qHom_Vq]

theorem qHom_wordProd
    (w : List ℤ) :
    qHom (wordProd uvQ w) = wordProd uvGen12 w := by
  rw [map_wordProd']
  simp only [qHom_uvQ]

theorem closure_uvQ :
    Subgroup.closure ({Uq, Vq} : Set QW) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({u, v} : Set (GL (Fin 112) (ZMod 2))))
  have e : Subgroup.map (QuotientGroup.mk' (P.subgroupOf W))
      (Subgroup.closure (Subtype.val ⁻¹' ({u, v} : Set (GL (Fin 112) (ZMod 2))))) = ⊤ := by
    rw [h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [MonoidHom.map_closure] at e
  rw [← e]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨⟨u, u_mem_W⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨v, v_mem_W⟩, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · left; exact congrArg _ (Subtype.ext hw)
    · right; exact congrArg _ (Subtype.ext hw)

@[expose] def wq :
    QW := wordProd uvQ normalThreeWord

@[expose] def zq :
    QW := wq ^ 11

@[expose] def hq :
    QW := wordProd uvQ secondConjugatorWord

@[expose] def xq :
    QW := wordProd uvQ firstBaseWord ^ 12

@[expose] def yq :
    QW := hq⁻¹ * wordProd uvQ secondBaseWord ^ 6 * hq

theorem PrRep12.pow {g : GL (Fin 12) (ZMod 2)} {x : Pr12} (hg : PrRep12 g x) (e : ℕ) :
    PrRep12 (g ^ e) (pr12Pow x e) := by
  induction e with
  | zero => rw [pow_zero]; exact PrRep12.one
  | succ e ih => rw [pow_succ]; exact ih.mul hg

theorem localChecks_eq : localChecks = true :=
  Certificates.certificate7016

theorem eq_of_rows12 {g h : GL (Fin 12) (ZMod 2)} {X Y : Array ℕ}
    (hg : CFSG.Sporadic.SmallF2.rowsMatrix 12 X = (g : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (hh : CFSG.Sporadic.SmallF2.rowsMatrix 12 Y = (h : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (e : (X == Y) = true) : g = h :=
  Units.ext (by rw [← hg, ← hh, beq_iff_eq.1 e])

theorem ne_of_rows12Ne {g h : GL (Fin 12) (ZMod 2)} {X Y : Array ℕ}
    (hg : CFSG.Sporadic.SmallF2.rowsMatrix 12 X = (g : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (hh : CFSG.Sporadic.SmallF2.rowsMatrix 12 Y = (h : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (e : rows12Ne X Y = true) : g ≠ h := by
  intro hgh
  simp only [rows12Ne, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at e
  obtain ⟨i, hi, j, hj, hne⟩ := e
  have := congrFun (congrFun (hg.trans ((congrArg Units.val hgh).trans hh.symm))
    ⟨i, hi⟩) ⟨j, hj⟩
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
    CFSG.Sporadic.SmallF2.toVecD_apply, CFSG.Sporadic.SmallF2.toVecD_apply] at this
  apply hne
  simp only [Array.getD_eq_getD_getElem?] at this ⊢
  revert this
  cases (X[i]?.getD 0).testBit j <;> cases (Y[i]?.getD 0).testBit j <;> simp

theorem prRep12_U :
    PrRep12 U12 (uvPairs12[0]?.getD pr12One) := famRep12_uv 0

theorem prRep12_V :
    PrRep12 V12 (uvPairs12[1]?.getD pr12One) := famRep12_uv 1

theorem prRep12_zq :
    PrRep12 (qHom zq) zPair := by
  rw [zq, map_pow, wq, qHom_wordProd]; exact (famRep12_uv.word _).pow 11

theorem prRep12_hq :
    PrRep12 (qHom hq) hPair := by
  rw [hq, qHom_wordProd]; exact famRep12_uv.word _

theorem prRep12_xq :
    PrRep12 (qHom xq) xPair := by
  rw [xq, map_pow, qHom_wordProd]; exact (famRep12_uv.word _).pow 12

theorem prRep12_yq :
    PrRep12 (qHom yq) yPair := by
  rw [yq, map_mul, map_mul, map_inv, map_pow, qHom_wordProd]
  exact (prRep12_hq.inv.mul ((famRep12_uv.word _).pow 6)).mul prRep12_hq

theorem rowsMatrix12_idRows_eq :
    CFSG.Sporadic.SmallF2.rowsMatrix 12 (CFSG.Sporadic.SmallF2.Native.idRows 12) =
      ((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_idRows, Units.val_one]

theorem localChecks_spec :
    zq ≠ 1 ∧ zq ^ 3 = 1 ∧ Uq * zq * Uq⁻¹ = zq⁻¹ ∧ Vq * zq = zq * Vq ∧
    xq * zq = zq * xq ∧ yq * zq = zq * yq ∧ xq ^ 2 = 1 ∧ yq ^ 4 = 1 ∧ (xq * yq) ^ 11 = zq ∧
    xq ≠ 1 := by
  have h := localChecks_eq
  simp only [localChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hz := prRep12_zq
  have hx := prRep12_xq
  have hy := prRep12_yq
  have hone := rowsMatrix12_idRows_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact ne_of_rows12Ne hz.1 hone h1 (by rw [e, map_one])
  · apply qHom_injective
    rw [map_pow, map_one]
    exact eq_of_rows12 (hz.pow 3).1 hone h2
  · apply qHom_injective
    rw [map_mul, map_mul, map_inv, map_inv, qHom_Uq]
    exact eq_of_rows12 ((prRep12_U.mul hz).mul prRep12_U.inv).1 hz.2 h3
  · apply qHom_injective
    rw [map_mul, map_mul, qHom_Vq]
    exact eq_of_rows12 (prRep12_V.mul hz).1 (hz.mul prRep12_V).1 h4
  · apply qHom_injective
    rw [map_mul, map_mul]
    exact eq_of_rows12 (hx.mul hz).1 (hz.mul hx).1 h5
  · apply qHom_injective
    rw [map_mul, map_mul]
    exact eq_of_rows12 (hy.mul hz).1 (hz.mul hy).1 h6
  · apply qHom_injective
    rw [map_pow, map_one]
    exact eq_of_rows12 (hx.pow 2).1 hone h7
  · apply qHom_injective
    rw [map_pow, map_one]
    exact eq_of_rows12 (hy.pow 4).1 hone h8
  · apply qHom_injective
    rw [map_pow, map_mul]
    exact eq_of_rows12 ((hx.mul hy).pow 11).1 hz.1 h9
  · intro e
    exact ne_of_rows12Ne hx.1 hone h10 (by rw [e, map_one])

end CFSG.Quasithin.H13.J4
