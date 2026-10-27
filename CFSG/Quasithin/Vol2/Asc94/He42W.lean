module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42FinB
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private theorem he42w_sup_eq_of_card {R Z Z' B : Subgroup G} (hZR : Z ≤ R) (hZ'R : Z' ≤ R)
    (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hR : Nat.card R = 64) (hZ : Nat.card Z = 16)
    (hZ' : Nat.card Z' = 16) (hint : Z ⊓ Z' ≤ B) (hBR : B ≤ R) (hB : Nat.card B = 4) :
    R ≤ Z ⊔ Z' := by
  haveI hZn : (Z.subgroupOf R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : (g : G) * (n : G) = (n : G) * (g : G) := hRc _ g.2 _ n.2
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hgn, mul_inv_cancel_right]
    rw [e]
    exact hn
  have hZr : Nat.card (Z.subgroupOf R) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, hZ]
  have hZ'r : Nat.card (Z'.subgroupOf R) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'R).toEquiv, hZ']
  have hint' : Nat.card ↥((Z.subgroupOf R) ⊓ (Z'.subgroupOf R)) ≤ 4 := by
    have hsub : (Z.subgroupOf R) ⊓ (Z'.subgroupOf R) ≤ B.subgroupOf R := by
      intro x hx
      apply Subgroup.mem_subgroupOf.mpr
      apply hint
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2⟩
    have h := Subgroup.card_le_of_le hsub
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR).toEquiv, hB] at h
    exact h
  have h1 : (Z.subgroupOf R).relIndex ((Z'.subgroupOf R) ⊔ (Z.subgroupOf R)) =
      (Z.subgroupOf R).relIndex (Z'.subgroupOf R) :=
    Subgroup.relIndex_sup_right (H := Z'.subgroupOf R) (K := Z.subgroupOf R)
  have h2 : (Z.subgroupOf R).relIndex (Z'.subgroupOf R) *
      Nat.card ↥((Z.subgroupOf R) ⊓ (Z'.subgroupOf R)) = Nat.card ↥(Z'.subgroupOf R) :=
    Subgroup.relIndex_mul_card _ _
  rw [hZ'r] at h2
  have h3 : (Z.subgroupOf R).relIndex ⊤ = 4 := by
    have h := Subgroup.relIndex_mul_card (H := Z.subgroupOf R) (K := (⊤ : Subgroup R))
    rw [inf_top_eq, hZr, Subgroup.card_top, hR] at h
    omega
  have h4 : (Z.subgroupOf R).relIndex ((Z'.subgroupOf R) ⊔ (Z.subgroupOf R)) *
      ((Z'.subgroupOf R) ⊔ (Z.subgroupOf R)).relIndex ⊤ = (Z.subgroupOf R).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex (H := Z.subgroupOf R)
      (K := (Z'.subgroupOf R) ⊔ (Z.subgroupOf R)) (L := ⊤) le_sup_right le_top
  have hx4 : 4 ≤ (Z.subgroupOf R).relIndex (Z'.subgroupOf R) := by
    rcases Nat.eq_zero_or_pos (Nat.card ↥((Z.subgroupOf R) ⊓ (Z'.subgroupOf R))) with h | h
    · rw [h, mul_zero] at h2
      omega
    · nlinarith
  have hy : ((Z'.subgroupOf R) ⊔ (Z.subgroupOf R)).relIndex ⊤ = 1 := by
    rw [h1, h3] at h4
    generalize ((Z'.subgroupOf R) ⊔ (Z.subgroupOf R)).relIndex ⊤ = y at h4 ⊢
    generalize (Z.subgroupOf R).relIndex (Z'.subgroupOf R) = x at h4 hx4
    rcases Nat.lt_or_ge y 2 with hy | hy
    · interval_cases y <;> omega
    · exfalso
      nlinarith
  have hTop : (⊤ : Subgroup R) ≤ (Z'.subgroupOf R) ⊔ (Z.subgroupOf R) :=
    Subgroup.relIndex_eq_one.mp hy
  intro r hr
  have hle : (Z'.subgroupOf R) ⊔ (Z.subgroupOf R) ≤ (Z ⊔ Z').subgroupOf R :=
    sup_le (Subgroup.subgroupOf_mono R le_sup_right) (Subgroup.subgroupOf_mono R le_sup_left)
  exact Subgroup.mem_subgroupOf.mp (hle (hTop (Subgroup.mem_top (⟨r, hr⟩ : R))))

private theorem he42w_mem_inf_comm {H K : Subgroup G} {x : G} (h : x ∈ H ⊓ K) : x ∈ K ⊓ H :=
  Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h).2, (Subgroup.mem_inf.mp h).1⟩

private theorem he42w_side {L K R P J B : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hPD : PData L K R J ψ) (hPJ : P ≤ J) (hBZ : B ≤ P ⊓ R) (hB4 : Nat.card B = 4)
    (hP64 : Nat.card P = 64) (hR64 : Nat.card R = 64) (hZ16 : Nat.card ↥(P ⊓ R) = 16)
    (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    {g : G} (hgL : g ∈ L) (hgK : g ∉ K) (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hsp : ∀ h ∈ L, h ∉ K → ∀ z ∈ P ⊓ R, h * z * h⁻¹ ∈ P ⊓ R → z ∈ B) :
    P ⊔ P.map (MulAut.conj g).toMonoidHom = L := by
  have hPK : P ≤ K := hPJ.trans hPD.JK
  have hPL : P ≤ L := hPK.trans hPD.KL
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = P ⊔ P.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  rw [← hWdef]
  have hPW : P ≤ W := by
    rw [hWdef]
    exact le_sup_left
  have hcW : ∀ x ∈ P, g * x * g⁻¹ ∈ W := fun x hx => by
    rw [hWdef]
    exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hWL : W ≤ L := by
    rw [hWdef]
    refine sup_le hPL ?_
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem hgL (hPL hx)) (L.inv_mem hgL)
  have hRW : R ≤ W := by
    have hZ'R : (P ⊓ R).map (MulAut.conj g).toMonoidHom ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hgR x (Subgroup.mem_inf.mp hx).2
    have hZ'c : Nat.card ↥((P ⊓ R).map (MulAut.conj g).toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ16]
    have hint : (P ⊓ R) ⊓ (P ⊓ R).map (MulAut.conj g).toMonoidHom ≤ B := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hx).2
      have hzx' : g * z * g⁻¹ = x := hzx
      have e : g⁻¹ * x * g⁻¹⁻¹ = z := by
        rw [← hzx', inv_inv]
        group
      exact hsp g⁻¹ (L.inv_mem hgL) (fun h => hgK (by simpa using K.inv_mem h)) x
        (Subgroup.mem_inf.mp hx).1 (by rw [e]; exact hz)
    have hcount := he42w_sup_eq_of_card (inf_le_right : P ⊓ R ≤ R) hZ'R hRc hR64 hZ16 hZ'c hint
      (hBZ.trans inf_le_right) hB4
    rw [hWdef]
    exact hcount.trans (sup_le ((inf_le_left : P ⊓ R ≤ P).trans le_sup_left)
      ((Subgroup.map_mono (inf_le_left : P ⊓ R ≤ P)).trans le_sup_right))
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (Equiv.Perm (Fin 5)), H = (P.subgroupOf L).map ψ :=
    ⟨_, rfl⟩
  have hHcard : Nat.card H = 4 := by
    have h1 := Subgroup.relIndex_ker (K := P.subgroupOf L) ψ
    rw [hPD.ker, Subgroup.relIndex_subgroupOf hPL] at h1
    have h2 := Subgroup.relIndex_mul_card (H := R) (K := P)
    rw [inf_comm R P, hZ16, hP64] at h2
    rw [hHdef, ← h1]
    omega
  have hHA : H ≤ alternatingGroup (Fin 5) := by
    rw [hHdef, ← hPD.range]
    exact Subgroup.map_le_range ψ _
  have hH0 : ∀ h ∈ H, h 0 = 0 := by
    intro h hh
    rw [hHdef] at hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hPD.stab k).mpr (hPK (Subgroup.mem_subgroupOf.mp hk))
  have hσA : ψ ⟨g, hgL⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hPD.range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hσ0 : ψ ⟨g, hgL⟩ 0 ≠ 0 := fun h => hgK ((hPD.stab ⟨g, hgL⟩).mp h)
  have hF5 : H ⊔ H.map (MulAut.conj (ψ ⟨g, hgL⟩)).toMonoidHom = alternatingGroup (Fin 5) :=
    CFSG.Quasithin.A94.He42Fin.sup_conj_klein_eq_alternating H hHA hH0 hHcard _ hσA hσ0
  have hAW : alternatingGroup (Fin 5) ≤ (W.subgroupOf L).map ψ := by
    rw [← hF5]
    refine sup_le ?_ ?_
    · rw [hHdef]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨k, Subgroup.mem_subgroupOf.mpr (hPW (Subgroup.mem_subgroupOf.mp hk)), rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [hHdef] at hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩ * k * ⟨g, hgL⟩⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (hcW _ (Subgroup.mem_subgroupOf.mp hk))
      · simp [MulAut.conj_apply, map_mul, map_inv]
  have hLW : L ≤ W := by
    intro l hl
    have hψl : ψ ⟨l, hl⟩ ∈ alternatingGroup (Fin 5) := by
      rw [← hPD.range]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨w, hw, hwl⟩ := Subgroup.mem_map.mp (hAW hψl)
    have hk : w⁻¹ * ⟨l, hl⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwl, inv_mul_cancel]
    rw [hPD.ker] at hk
    have hr : (w : G)⁻¹ * l ∈ R := by
      simpa using Subgroup.mem_subgroupOf.mp hk
    have hm := W.mul_mem (Subgroup.mem_subgroupOf.mp hw) (hRW hr)
    simpa using hm
  exact le_antisymm hWL hLW

theorem HeSetup.stepW (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) (hSp : S.StepSpread) :
    S.StepW := by
  obtain ⟨⟨ψ₁, hP₁⟩, ⟨ψ₂, hP₂⟩⟩ := hP
  unfold HeSetup.StepW
  refine ⟨fun g hg hgK => ?_, fun g hg hgK => ?_⟩
  · exact he42w_side hP₂ hB.A_le_J hB.B_le_Z hB.card_B hB.card_A hB.card_A' hB.card_Z hB.A'_comm
      hg hgK (fun r hr => (Subgroup.mem_normalizer_iff.mp (hB.L2_le_normalizer hg) r).mp hr)
      (fun h hh hhK z hz hz' => hSp.2 h hh hhK z hz hz')
  · have hZ' : Nat.card ↥(S.A' ⊓ S.A) = 16 := by
      rw [inf_comm]
      exact hB.card_Z
    exact he42w_side hP₁ hB.A'_le_J (hB.B_le_Z.trans (inf_comm S.A S.A').le) hB.card_B
      hB.card_A' hB.card_A hZ' hB.A_comm hg hgK
      (fun r hr => (Subgroup.mem_normalizer_iff.mp (hB.L1_le_normalizer hg) r).mp hr)
      (fun h hh hhK z hz hz' => hSp.1 h hh hhK z (he42w_mem_inf_comm hz)
        (he42w_mem_inf_comm hz'))

end CFSG.Quasithin.A94.He42
