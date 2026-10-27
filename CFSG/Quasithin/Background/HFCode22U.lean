module

public import CFSG.Quasithin.Background.HFCode22
public import CFSG.Quasithin.Background.HB82Code22
public import Certificates.Certificate7248

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Code22

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem mem_fixV_map_congrHom_iff' {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (X : Subgroup (MulAut V)) (w : W) : w ∈ fixV (X.map (congrHom e)) ↔ e.symm w ∈ fixV X :=
  mem_fixV_map_congr_equiv e X w

theorem congrHom_trans_eq_conj {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (c : MulAut W) (x : MulAut V) : congrHom (e.trans c) x = c * congrHom e x * c⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem hfU22Greedy {k : ℕ}
    (hk : k ≤ 5) : forallGreedy T22s2.invols predU22 k [] = true :=
  (forallGreedyP_eq pos22s2_eq predU22 k []).symm.trans
    (forallGreedyAll_le 5 [] Certificates.certificate7248.1 k hk)

theorem code22_E32_std
    {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (h : MathieuCode22 H ⊤ ⊥) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) (hX : Nat.card ↥X = 2 ^ 5) (_hfX : Nat.card ↥(fixV X) = 2 ^ 4) :
    ∃ e : V ≃* W10, H.map (congrHom e) = imgC mog22 ∧
      fixV (X.map (congrHom e)) = maskSub 10 [19, 194, 354, 513] := by
  have hLM : IsOver H (Subgroup.normalizer (H : Set (MulAut V))) :=
    ⟨Subgroup.le_normalizer, le_rfl⟩
  obtain ⟨e, he⟩ := code22_std h
  have hXe2 : IsElemAbelian2 X := isElemAbelian2_iff.2 hXe
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective
    phi22 (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    (hfU22Greedy le_rfl) e (map_le_rangeC22 hLM he hXN) hXe2 hX
  have hcl := card_of_chainSub hchain (chainAutC22_injective e g) hind
  rw [hX] at hcl
  have hlen : l.length = 5 := (Nat.pow_right_injective (le_refl 2) hcl).symm
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hfix : fixMasks 10 codeAct22 l = u22Masks := by
    rw [← codeFixMasks22_eq hinv]
    simp only [predU22, hlen, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hpred
    exact hpred
  set e' := twistEquiv e psiC22 g with he'
  have hc := chainActC22 e g
  refine ⟨e', ?_, ?_⟩
  ·
    have hN : psiC22 g ∈ Subgroup.normalizer
        ((rhoC10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) := by
      rw [normalizer_rhoC10_mog22]
      exact ⟨g, rfl⟩
    rw [← range_rhoC10_eq_imgC]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxr : congrHom e x ∈ (rhoC10 mog22 mog22_le_mog22plus).range := by
        rw [← he]
        exact ⟨x, hx, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp hxr
      have h3 := congrHom_trans_eq_conj e (psiC22 g) x
      exact (congrArg (· ∈ (rhoC10 mog22 mog22_le_mog22plus).range) h3).mpr h2
    · rintro _ ⟨k, rfl⟩
      have hk : rhoC10 mog22 mog22_le_mog22plus k ∈ (rhoC10 mog22 mog22_le_mog22plus).range :=
        ⟨k, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) _).mp hk
      rw [← he] at h1
      obtain ⟨x, hx, hxe⟩ := h1
      refine ⟨x, hx, MulEquiv.ext fun w => ?_⟩
      have h4 : congrHom e x ((psiC22 g)⁻¹ w) =
          (psiC22 g)⁻¹ (rhoC10 mog22 mog22_le_mog22plus k w) := by
        have := congrArg (fun f : MulAut W10 => f ((psiC22 g)⁻¹ w)) hxe
        simp only [MulAut.mul_apply, inv_inv, MulAut.apply_inv_self] at this
        exact this
      show psiC22 g (congrHom e x ((psiC22 g)⁻¹ w)) = _
      rw [h4, MulAut.apply_inv_self]
      rfl
  ·
    ext w
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
    refine (mem_fixV_map_congrHom_iff' e' X _).trans ?_
    change (MaskCoords.ofEquiv e').vm m ∈ fixV X ↔ _
    rw [vm_mem_fixV_iff hc hchain hm]
    have h2 : (l.all fun s => codeAct22 s m == m) = true ↔ m ∈ fixMasks 10 codeAct22 l := by
      have hm' : m < 1024 := hm
      simp [fixMasks, List.mem_range, hm']
    rw [h2, hfix]
    have h3 := toW_mem_UC_iff hm
    rw [show (u22Masks : List ℕ) = hbU0Masks from rfl]
    exact h3.symm

end CFSG.Quasithin.H.Mathieu
