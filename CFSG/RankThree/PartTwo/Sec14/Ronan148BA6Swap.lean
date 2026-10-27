module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Img
public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KTransport148 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G) (c : G), Sec14Std G A c L →
    ∀ B : Subgroup G, IsHyperplane A B → ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
    ∀ YB : Subgroup G, YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
    ∀ E : Subgroup G, E ≤ YB → IsPGroup 3 E → Nat.card E = 9 →
      ∃ u ∈ Subgroup.centralizer ({b} : Set G),
        A.map (MulAut.conj u).toMonoidHom = Subgroup.zpowers b ⊔ E ∧
          (A ⊓ Lb).map (MulAut.conj u).toMonoidHom = E

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_eq_conj_of_mem_map {H : Subgroup G} {g z : G}
    (hz : z ∈ H.map (MulAut.conj g).toMonoidHom) : ∃ h ∈ H, z = g * h * g⁻¹ := by
  obtain ⟨h, hh, rfl⟩ := hz
  exact ⟨h, hh, by simp [MulAut.conj_apply]⟩

theorem exists_normalizer_mem_inf148 (hT : KTransport148) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb) (hbA : b ∈ A) (hdA : d ∈ A) {YB : Subgroup G} (hYBY : YB ≤ Y)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B) {y : G} (hy : y ∈ Y)
    (hE9 : Nat.card ↥(Subgroup.zpowers (alpha148 A Y b hbA) ⊔
      Subgroup.zpowers (alpha148 A Y d hdA)) = 9)
    (hEx : (Subgroup.zpowers (alpha148 A Y b hbA) ⊔ Subgroup.zpowers (alpha148 A Y d hdA)).map
      (MulAut.conj (QuotientGroup.mk' (ker148 A Y) ⟨y, Subgroup.mem_sup_left hy⟩)).toMonoidHom ≤
        img148 A Y YB)
    (hEx' : (Subgroup.zpowers (alpha148 A Y b hbA) ⊔ Subgroup.zpowers (alpha148 A Y d hdA)).map
      (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
        ⟨y, Subgroup.mem_sup_left hy⟩)⁻¹).toMonoidHom ≤ img148 A Y YB)
    (hdx : (Subgroup.zpowers (alpha148 A Y d hdA)).map
      (MulAut.conj (QuotientGroup.mk' (ker148 A Y) ⟨y, Subgroup.mem_sup_left hy⟩)).toMonoidHom =
        Subgroup.zpowers (alpha148 A Y d hdA)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w * b * w⁻¹ ∈ A ⊓ Lb := by
  have hA : Late.IsE27 A := hS.isE27
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
  have hbM : b ∈ Y ⊔ A := Subgroup.mem_sup_right hbA
  obtain ⟨x, hx⟩ : ∃ x, x = QuotientGroup.mk' (ker148 A Y) (⟨y, hyM⟩ : ↥(Y ⊔ A)) := ⟨_, rfl⟩
  obtain ⟨bα, hbαdef⟩ : ∃ bα, bα = alpha148 A Y b hbA := ⟨_, rfl⟩
  obtain ⟨dα, hdαdef⟩ : ∃ dα, dα = alpha148 A Y d hdA := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = Subgroup.zpowers bα ⊔ Subgroup.zpowers dα := ⟨_, rfl⟩
  rw [← hx, ← hbαdef, ← hdαdef, ← hEdef] at hEx hEx'
  rw [← hx, ← hdαdef] at hdx
  rw [← hbαdef, ← hdαdef, ← hEdef] at hE9
  have hYBM : YB ≤ Y ⊔ A := hYBY.trans le_sup_left
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨E₁, hE₁YB, hE₁p, hE₁img, hE₁c⟩ := exists_le_img148_eq hEx (hE3.map _)
  obtain ⟨E₂, hE₂YB, hE₂p, hE₂img, hE₂c⟩ := exists_le_img148_eq hEx' (hE3.map _)
  have hc₁ : Nat.card E₁ = 9 := by
    rw [hE₁c, Subgroup.card_map_of_injective (MulAut.conj x).injective, hE9]
  have hc₂ : Nat.card E₂ = 9 := by
    rw [hE₂c, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hE9]
  obtain ⟨u₁, hu₁, hAu₁, -⟩ := hT G A L c hS B hB b d Lb hc YB hle E₁ hE₁YB hE₁p hc₁
  obtain ⟨u, -, hAu, hALu⟩ := hT G A L c hS B hB b d Lb hc YB hle E₂ hE₂YB hE₂p hc₂
  have hF₁M : Subgroup.zpowers b ⊔ E₁ ≤ Y ⊔ A :=
    sup_le (Subgroup.zpowers_le.mpr hbM) (hE₁YB.trans hYBM)
  have hF₂'M : Subgroup.zpowers b ⊔ E₂ ≤ Y ⊔ A :=
    sup_le (Subgroup.zpowers_le.mpr hbM) (hE₂YB.trans hYBM)
  have hF₂M : (Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom ≤ Y ⊔ A := by
    rintro _ ⟨z, hz, rfl⟩
    have hzM := hF₂'M hz
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    exact (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hyM hzM) ((Y ⊔ A).inv_mem hyM)
  have hAF₂ : A.map (MulAut.conj (y * u)).toMonoidHom =
      (Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom := by
    rw [← hAu, Res2LBal.map_conj_map_conj]
  have hF₁p : IsPGroup 3 ↥(Subgroup.zpowers b ⊔ E₁) := by rw [← hAu₁]; exact hAp.map _
  have hF₂p : IsPGroup 3 ↥((Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom) := by
    rw [← hAF₂]; exact hAp.map _
  have hcard : Nat.card ↥((Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom) =
      Nat.card ↥(Subgroup.zpowers b ⊔ E₁) := by
    rw [← hAF₂, ← hAu₁, Subgroup.card_map_of_injective (MulAut.conj (y * u)).injective,
      Subgroup.card_map_of_injective (MulAut.conj u₁).injective]
  have hbα : QuotientGroup.mk' (ker148 A Y) (⟨b, hbM⟩ : ↥(Y ⊔ A)) = bα := by
    rw [hbαdef]; rfl
  have hEx2 : (E.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = E := by
    rw [Res2LBal.map_conj_map_conj, mul_inv_cancel, Res2LBal.map_conj_one]
  have hEmap : E.map (MulAut.conj x).toMonoidHom =
      Subgroup.zpowers (x * bα * x⁻¹) ⊔ Subgroup.zpowers dα := by
    rw [hEdef, Subgroup.map_sup, hdx, MonoidHom.map_zpowers]
    rfl
  have hL : img148 A Y (Subgroup.zpowers b ⊔ E₁) =
      Subgroup.zpowers bα ⊔ (Subgroup.zpowers (x * bα * x⁻¹) ⊔ Subgroup.zpowers dα) := by
    rw [img148_sup (Subgroup.zpowers_le.mpr hbM) (hE₁YB.trans hYBM), img148_zpowers hbM, hE₁img,
      hbα, hEmap]
  have hR : img148 A Y ((Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom) =
      Subgroup.zpowers (x * bα * x⁻¹) ⊔ (Subgroup.zpowers bα ⊔ Subgroup.zpowers dα) := by
    rw [img148_map_conj hF₂'M hyM, img148_sup (Subgroup.zpowers_le.mpr hbM) (hE₂YB.trans hYBM),
      img148_zpowers hbM, hE₂img, hbα, ← hx, Subgroup.map_sup, hEx2, MonoidHom.map_zpowers, hEdef]
    rfl
  have himg : img148 A Y (Subgroup.zpowers b ⊔ E₁) =
      img148 A Y ((Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom) := by
    rw [hL, hR, sup_left_comm]
  obtain ⟨κ, hκ, hκF⟩ := exists_conj_eq_of_img148_eq hF₁M hF₂M hF₁p hcard himg
  have hκY : κ ∈ Y := pPrimeCoreOf_le 3 Y hκ
  have hκM : κ ∈ Y ⊔ A := Subgroup.mem_sup_left hκY
  refine ⟨(y * u)⁻¹ * κ * u₁, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change A.map (MulAut.conj ((y * u)⁻¹ * κ * u₁)).toMonoidHom = A
    rw [← Res2LBal.map_conj_map_conj, ← Res2LBal.map_conj_map_conj, hAu₁, ← hκF, ← hAF₂,
      Res2LBal.map_conj_map_conj, inv_mul_cancel, Res2LBal.map_conj_one]
  · have hu₁b : u₁ * b * u₁⁻¹ = b := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hu₁
      rw [hu₁, mul_inv_cancel_right]
    have e1 : (y * u)⁻¹ * κ * u₁ * b * ((y * u)⁻¹ * κ * u₁)⁻¹ =
        (y * u)⁻¹ * (κ * b * κ⁻¹) * (y * u) := by
      calc (y * u)⁻¹ * κ * u₁ * b * ((y * u)⁻¹ * κ * u₁)⁻¹ =
          (y * u)⁻¹ * κ * (u₁ * b * u₁⁻¹) * κ⁻¹ * (y * u) := by group
        _ = _ := by rw [hu₁b]; group
    rw [e1]
    have hbF₁ : b ∈ Subgroup.zpowers b ⊔ E₁ := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    have hfF₂ : κ * b * κ⁻¹ ∈ (Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom := by
      rw [hκF]
      exact ⟨b, hbF₁, by simp [MulAut.conj_apply]⟩
    have hfM : κ * b * κ⁻¹ ∈ Y ⊔ A := hF₂M hfF₂
    have hfα : QuotientGroup.mk' (ker148 A Y) (⟨κ * b * κ⁻¹, hfM⟩ : ↥(Y ⊔ A)) = bα := by
      have hκ1 : QuotientGroup.mk' (ker148 A Y) (⟨κ, hκM⟩ : ↥(Y ⊔ A)) = 1 :=
        mk'_ker148_eq_one_iff.mpr hκ
      have e2 : (⟨κ * b * κ⁻¹, hfM⟩ : ↥(Y ⊔ A)) = ⟨κ, hκM⟩ * ⟨b, hbM⟩ * ⟨κ, hκM⟩⁻¹ := rfl
      rw [e2, map_mul, map_mul, map_inv, hκ1, one_mul, inv_one, mul_one]
      exact hbα
    have hbE : bα ∈ img148 A Y (E₂.map (MulAut.conj y).toMonoidHom) := by
      rw [img148_map_conj (hE₂YB.trans hYBM) hyM, hE₂img, ← hx, hEx2, hEdef]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers bα)
    obtain ⟨g, hgM, hgE, hgα⟩ := mem_img148_iff.mp hbE
    have hgF₂ : g ∈ (Subgroup.zpowers b ⊔ E₂).map (MulAut.conj y).toMonoidHom :=
      Subgroup.map_mono le_sup_right hgE
    have hfg : κ * b * κ⁻¹ = g :=
      eq_of_mk'_eq_of_isPGroup hF₂p hfF₂ hgF₂ hfM hgM (hfα.trans hgα.symm)
    rw [hfg]
    obtain ⟨e', he', rfl⟩ := exists_eq_conj_of_mem_map hgE
    rw [← hALu] at he'
    obtain ⟨a', ha', rfl⟩ := exists_eq_conj_of_mem_map he'
    have e3 : (y * u)⁻¹ * (y * (u * a' * u⁻¹) * y⁻¹) * (y * u) = a' := by group
    rw [e3]
    exact ha'

theorem exists_normalizer_map_inf148 (hT : KTransport148) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} [(ker148 A Y).Normal] {B : Subgroup G}
    (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hbA : b ∈ A) {YB : Subgroup G} (hYBY : YB ≤ Y)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {E₁ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hE₁ : E₁ ≤ img148 A Y YB) (hE₁3 : IsPGroup 3 E₁)
    (hE₁9 : Nat.card E₁ = 9)
    (hAeq : Subgroup.zpowers (alpha148 A Y b hbA) ⊔ E₁ = img148 A Y A) :
    ∃ w₁ ∈ Subgroup.normalizer (A : Set G), ∀ e ∈ A ⊓ Lb,
      ∃ he : w₁ * e * w₁⁻¹ ∈ A, alpha148 A Y (w₁ * e * w₁⁻¹) he ∈ E₁ := by
  have hA : Late.IsE27 A := hS.isE27
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hYBM : YB ≤ Y ⊔ A := hYBY.trans le_sup_left
  have hbM : b ∈ Y ⊔ A := Subgroup.mem_sup_right hbA
  obtain ⟨Et, hEtYB, hEtp, hEtimg, hEtc⟩ := exists_le_img148_eq hE₁ hE₁3
  obtain ⟨u₂, -, hAu₂, hALu₂⟩ := hT G A L c hS B hB b d Lb hc YB hle Et hEtYB hEtp
    (hEtc.trans hE₁9)
  have hFM : Subgroup.zpowers b ⊔ Et ≤ Y ⊔ A :=
    sup_le (Subgroup.zpowers_le.mpr hbM) (hEtYB.trans hYBM)
  have hcard : Nat.card ↥(Subgroup.zpowers b ⊔ Et) = Nat.card A := by
    rw [← hAu₂, Subgroup.card_map_of_injective (MulAut.conj u₂).injective]
  have himg : img148 A Y A = img148 A Y (Subgroup.zpowers b ⊔ Et) := by
    rw [img148_sup (Subgroup.zpowers_le.mpr hbM) (hEtYB.trans hYBM), img148_zpowers hbM,
      hEtimg, ← hAeq]
    rfl
  obtain ⟨κ, hκ, hκF⟩ := exists_conj_eq_of_img148_eq le_sup_right hFM hAp hcard himg
  have hκM : κ ∈ Y ⊔ A := Subgroup.mem_sup_left (pPrimeCoreOf_le 3 Y hκ)
  refine ⟨κ⁻¹ * u₂, ?_, fun e he => ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change A.map (MulAut.conj (κ⁻¹ * u₂)).toMonoidHom = A
    rw [← Res2LBal.map_conj_map_conj, hAu₂, hκF, Res2LBal.map_conj_map_conj,
      inv_mul_cancel, Res2LBal.map_conj_one]
  · have hzEt : u₂ * e * u₂⁻¹ ∈ Et := by
      rw [← hALu₂]
      exact ⟨e, he, by simp [MulAut.conj_apply]⟩
    have hzF : u₂ * e * u₂⁻¹ ∈ A.map (MulAut.conj κ).toMonoidHom := by
      rw [← hκF]
      exact Subgroup.mem_sup_right hzEt
    obtain ⟨a', ha', ha'eq⟩ := exists_eq_conj_of_mem_map hzF
    have e1 : κ⁻¹ * u₂ * e * (κ⁻¹ * u₂)⁻¹ = a' := by
      calc κ⁻¹ * u₂ * e * (κ⁻¹ * u₂)⁻¹ = κ⁻¹ * (u₂ * e * u₂⁻¹) * κ := by group
        _ = a' := by rw [ha'eq]; group
    refine ⟨e1 ▸ ha', ?_⟩
    have hzM : u₂ * e * u₂⁻¹ ∈ Y ⊔ A := hYBM (hEtYB hzEt)
    have hzα : QuotientGroup.mk' (ker148 A Y) (⟨u₂ * e * u₂⁻¹, hzM⟩ : ↥(Y ⊔ A)) ∈ E₁ := by
      rw [← hEtimg]
      exact mem_img148_iff.mpr ⟨_, hzM, hzEt, rfl⟩
    have hκ1 : QuotientGroup.mk' (ker148 A Y) (⟨κ, hκM⟩ : ↥(Y ⊔ A)) = 1 :=
      mk'_ker148_eq_one_iff.mpr hκ
    have e2 : alpha148 A Y (κ⁻¹ * u₂ * e * (κ⁻¹ * u₂)⁻¹) (e1 ▸ ha') =
        QuotientGroup.mk' (ker148 A Y) (⟨u₂ * e * u₂⁻¹, hzM⟩ : ↥(Y ⊔ A)) := by
      rw [alpha148_eq_mk']
      have e3 : (⟨κ⁻¹ * u₂ * e * (κ⁻¹ * u₂)⁻¹, Subgroup.mem_sup_right (e1 ▸ ha')⟩ : ↥(Y ⊔ A)) =
          (⟨κ, hκM⟩ : ↥(Y ⊔ A))⁻¹ * ⟨u₂ * e * u₂⁻¹, hzM⟩ * ⟨κ, hκM⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
      rw [e3, map_mul, map_mul, map_inv, hκ1, inv_one, one_mul, mul_one]
    rw [e2]
    exact hzα

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
