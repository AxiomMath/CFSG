module

public import CFSG.Quasithin.Background.B3ThreeGen
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.B3

variable (n : ℕ)

@[expose] def permModEquiv : G6.PermMod n ≃* B3.U n where
  toFun x := ⟨Multiplicative.toAdd x⟩
  invFun w := Multiplicative.ofAdd w.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {n}

theorem permModEquiv_permAct (σ : Equiv.Perm (Fin n)) (x : G6.PermMod n) :
    permModEquiv n (G6.permAct n σ x) = B3.permAct n σ (permModEquiv n x) := rfl

theorem mem_coreMod_iff (x : G6.PermMod n) : x ∈ G6.coreMod n ↔ permModEquiv n x ∈ U0 n := by
  rw [G6.mem_coreMod]
  show _ ↔ Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i) = 1
  rw [ofAdd_eq_one]

theorem map_coreMod : (G6.coreMod n).map (permModEquiv n).toMonoidHom = U0 n := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_coreMod_iff x).1 hx
  · intro hw
    refine ⟨(permModEquiv n).symm w, ?_, (permModEquiv n).apply_symm_apply w⟩
    show (permModEquiv n).symm w ∈ G6.coreMod n
    rw [mem_coreMod_iff, MulEquiv.apply_symm_apply]
    exact hw

theorem map_zpowers_allOnes :
    (Subgroup.zpowers (G6.allOnes n)).map (permModEquiv n).toMonoidHom = Esub n := by
  rw [MonoidHom.map_zpowers]
  rfl

@[expose] noncomputable def coreEquiv : ↥(G6.coreMod n) ≃* ↥(U0 n) :=
  ((permModEquiv n).subgroupMap (G6.coreMod n)).trans (MulEquiv.subgroupCongr map_coreMod)

theorem coreEquiv_coe (x : ↥(G6.coreMod n)) :
    ((coreEquiv x : ↥(U0 n)) : B3.U n) = permModEquiv n x := rfl

theorem map_coreEquiv_ker :
    ((Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n)).map
      (coreEquiv (n := n)).toMonoidHom = (Esub n).subgroupOf (U0 n) := by
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, coreEquiv_coe, ← map_zpowers_allOnes]
    exact ⟨x, hx, rfl⟩
  · intro hw
    refine ⟨coreEquiv.symm w, ⟨?_, (coreEquiv.symm w).2⟩, coreEquiv.apply_symm_apply w⟩
    rw [← map_zpowers_allOnes] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    have : ((coreEquiv.symm w : ↥(G6.coreMod n)) : G6.PermMod n) = y := by
      apply (permModEquiv n).injective
      rw [← coreEquiv_coe, MulEquiv.apply_symm_apply]
      exact hyw.symm
    rw [this]
    exact hy

@[expose] noncomputable def dnEquiv :
    (↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Mod.V n Mod.ut0 :=
  QuotientGroup.congr _ _ coreEquiv map_coreEquiv_ker

theorem dnEquiv_mk_act (σ : ↥(alternatingGroup (Fin n))) (x : ↥(FFModel.altDn n).sec)
    (hx : (FFModel.altDn n).act σ (x : (FFModel.altDn n).Amb) ∈ (FFModel.altDn n).sec) :
    dnEquiv (QuotientGroup.mk ⟨(FFModel.altDn n).act σ x, hx⟩) =
      actL n Mod.ut0 σ (dnEquiv (QuotientGroup.mk x)) := by
  rfl

end CFSG.Quasithin.B513N
