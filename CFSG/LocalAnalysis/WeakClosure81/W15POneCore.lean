module

public import CFSG.LocalAnalysis.WeakClosure81.SevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

private theorem w15p_core_exists_eq_commutator [Finite G] {P : Subgroup G} {y : G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hyP : ∀ a ∈ P, y * a * y⁻¹ ∈ P)
    (hfix : ∀ a ∈ P, y * a * y⁻¹ = a → a = 1) :
    ∀ p ∈ P, ∃ a ∈ P, p = ⁅y, a⁆ := by
  let f : P → P :=
    fun z => ⟨y * (z : G) * y⁻¹ * (z : G)⁻¹, P.mul_mem (hyP z z.2) (P.inv_mem z.2)⟩
  have hinj : Function.Injective f := by
    intro z z' h
    apply Subtype.ext
    have h1 : y * (z : G) * y⁻¹ * (z : G)⁻¹ = y * (z' : G) * y⁻¹ * (z' : G)⁻¹ :=
      congrArg Subtype.val h
    have hcP : y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ P :=
      P.mul_mem (hyP z z.2) (P.inv_mem z.2)
    have hw : (z : G) * (z' : G)⁻¹ ∈ P := P.mul_mem z.2 (P.inv_mem z'.2)
    set c : G := y * (z : G) * y⁻¹ * (z : G)⁻¹ with hc
    have e1 : y * (z : G) * y⁻¹ = c * (z : G) := by rw [hc]; group
    have e2 : y * (z' : G) * y⁻¹ = c * (z' : G) := by rw [h1]; group
    have h2 : y * ((z : G) * (z' : G)⁻¹) * y⁻¹ = (z : G) * (z' : G)⁻¹ := by
      calc y * ((z : G) * (z' : G)⁻¹) * y⁻¹
          = (y * (z : G) * y⁻¹) * (y * (z' : G) * y⁻¹)⁻¹ := by group
        _ = (c * (z : G)) * (c * (z' : G))⁻¹ := by rw [e1, e2]
        _ = c * ((z : G) * (z' : G)⁻¹) * c⁻¹ := by group
        _ = ((z : G) * (z' : G)⁻¹) * c * c⁻¹ := by rw [hcomm c hcP _ hw]
        _ = (z : G) * (z' : G)⁻¹ := by group
    exact mul_inv_eq_one.1 (hfix _ hw h2)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro p hp
  obtain ⟨a, ha⟩ := hsurj ⟨p, hp⟩
  refine ⟨a, a.2, ?_⟩
  rw [commutatorElement_def]
  exact (congrArg Subtype.val ha).symm

theorem sup_nVSub_bSub_inf_centralizer_mul_eq_bot [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g v x : G} (hv : v ∈ V)
    (hvD : v ∉ nVSub V g) (hx : x ∈ conjSubgroup V g) (hxB : x ∉ bSub V g) :
    (nVSub V g ⊔ bSub V g) ⊓ centralizer ({v * x} : Set G) = ⊥ := by
  have hg : conjSubgroup V g ≠ V := by
    intro h
    exact hvD (by rw [nVSub, h]; exact ⟨hv, Subgroup.le_normalizer hv⟩)
  apply le_bot_iff.mp
  intro p hp
  obtain ⟨hpP, hpC⟩ := Subgroup.mem_inf.mp hp
  obtain ⟨d, hd, b, hb, rfl⟩ := exists_mul_of_mem_sup_nVSub_bSub hV hTI hg hpP
  have hcomm : d * b * (v * x) = v * x * (d * b) :=
    Subgroup.mem_centralizer_singleton_iff.mp hpC
  have hfix : v * x * (d * b) * (v * x)⁻¹ = d * b := by
    rw [← hcomm]; group
  have hconj : x * (d * b) * x⁻¹ = v⁻¹ * (d * b) * v := by
    have h1 : v * (x * (d * b) * x⁻¹) * v⁻¹ = d * b := by
      calc v * (x * (d * b) * x⁻¹) * v⁻¹
          = v * x * (d * b) * (v * x)⁻¹ := by group
        _ = d * b := hfix
    calc x * (d * b) * x⁻¹
        = v⁻¹ * (v * (x * (d * b) * x⁻¹) * v⁻¹) * v := by group
      _ = v⁻¹ * (d * b) * v := by rw [h1]
  have hxd : x * d * x⁻¹ = ⁅x, d⁆ * d := by rw [commutatorElement_def]; group
  have hxb : x * b * x⁻¹ = b := by
    rw [CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm (isElemAbelian_conjSubgroup' hV g) hx
      (mem_bSub.mp hb).1]
    group
  have hvd : v⁻¹ * d * v = d := by
    rw [CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hV (V.inv_mem hv) (mem_nVSub.mp hd).1]
    group
  have hvb : v⁻¹ * b * v = ⁅v⁻¹, b⁆ * b := by rw [commutatorElement_def]; group
  have hL : x * (d * b) * x⁻¹ = ⁅x, d⁆ * (d * b) := by
    rw [show x * (d * b) * x⁻¹ = (x * d * x⁻¹) * (x * b * x⁻¹) by group, hxd, hxb]
    group
  have hR : v⁻¹ * (d * b) * v = d * (⁅v⁻¹, b⁆ * b) := by
    rw [show v⁻¹ * (d * b) * v = (v⁻¹ * d * v) * (v⁻¹ * b * v) by group, hvd, hvb]
  have hmain : ⁅x, d⁆ * (d * b) = d * (⁅v⁻¹, b⁆ * b) := by
    rw [← hL, ← hR]
    exact hconj
  have hcde : ⁅x, d⁆ * d = d * ⁅v⁻¹, b⁆ :=
    mul_right_cancel (by simpa only [mul_assoc] using hmain)
  have hc : ⁅x, d⁆ ∈ bSub V g := commutator_mem_bSub hV hTI hx hd
  have he : ⁅v⁻¹, b⁆ ∈ nVSub V g := commutator_mem_nVSub hV hTI (V.inv_mem hv) hb
  have hdc : d * ⁅x, d⁆ = ⁅x, d⁆ * d := nVSub_comm_bSub hTI hg hd hc
  have hce : ⁅x, d⁆ = ⁅v⁻¹, b⁆ := by
    have h1 : d * ⁅v⁻¹, b⁆ = d * ⁅x, d⁆ := by rw [hcde.symm, hdc]
    exact (mul_left_cancel h1).symm
  have hcbot : ⁅x, d⁆ = 1 := by
    have hmem : ⁅x, d⁆ ∈ (⊥ : Subgroup G) := by
      rw [← nVSub_inf_bSub_eq_bot hTI hg]
      exact ⟨hce.symm ▸ he, hc⟩
    exact Subgroup.mem_bot.mp hmem
  have hxd1 : x * d * x⁻¹ = d := by rw [hxd, hcbot, one_mul]
  have hdx : d * x = x * d := by
    have h2 : x * d = d * x := by
      calc x * d = (x * d * x⁻¹) * x := by group
        _ = d * x := by rw [hxd1]
    exact h2.symm
  have hd1 : d = 1 := by
    have hmem : d ∈ nVSub V g ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr hdx⟩
    rw [nVSub_inf_centralizer_eq_bot hTI hg hx hxB] at hmem
    exact Subgroup.mem_bot.mp hmem
  have he1 : ⁅v⁻¹, b⁆ = 1 := hce ▸ hcbot
  have hvb1 : v⁻¹ * b * v = b := by rw [hvb, he1, one_mul]
  have hbv : b * v = v * b := by
    calc b * v = v * (v⁻¹ * b * v) := by group
      _ = v * b := by rw [hvb1]
  have hb1 : b = 1 := by
    have hmem : b ∈ bSub V g ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr hbv⟩
    rw [bSub_inf_centralizer_eq_bot hTI hg hv hvD] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [hd1, hb1, mul_one]
  exact Subgroup.mem_bot.mpr rfl

theorem nVSub_le_of_commutator_mem [Finite G] {V O : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V) (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hD : nVSub V g ≠ V)
    (hB : bSub V g ≠ conjSubgroup V g) (hOM : O ≤ normalizer (V : Set G))
    (hOg : conjSubgroup O g = O)
    (hcomm : ∀ m ∈ normalizer (V : Set G), ∀ w ∈ V, ⁅m, w⁆ ∈ O) :
    nVSub V g ≤ O := by
  have hg : conjSubgroup V g ≠ V := by
    intro h
    apply hD
    rw [nVSub, h]
    exact inf_eq_left.mpr Subgroup.le_normalizer
  obtain ⟨v, hvV, hvD⟩ := SetLike.exists_of_lt (lt_of_le_of_ne inf_le_left hD)
  obtain ⟨x, hxW, hxB⟩ := SetLike.exists_of_lt (lt_of_le_of_ne inf_le_left hB)
  have hPab : IsElemAbelian 2 (nVSub V g ⊔ bSub V g) :=
    isElemAbelian_sup_nVSub_bSub hV hTI hg
  have hcommP : ∀ a ∈ nVSub V g ⊔ bSub V g, ∀ b ∈ nVSub V g ⊔ bSub V g,
      a * b = b * a := fun a ha b hb =>
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hPab ha hb
  have hyX : v * x ∈ V ⊔ conjSubgroup V g :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hvV) (Subgroup.mem_sup_right hxW)
  have hyN : v * x ∈ normalizer ((nVSub V g ⊔ bSub V g : Subgroup G) : Set G) :=
    sup_le_normalizer_sup_nVSub_bSub hV hTI hg hyX
  have hyP : ∀ a ∈ nVSub V g ⊔ bSub V g,
      v * x * a * (v * x)⁻¹ ∈ nVSub V g ⊔ bSub V g := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
  have hfix : ∀ a ∈ nVSub V g ⊔ bSub V g, v * x * a * (v * x)⁻¹ = a → a = 1 := by
    intro a ha hafix
    have h2 : v * x * a = a * (v * x) := by
      calc v * x * a = (v * x * a * (v * x)⁻¹) * (v * x) := by group
        _ = a * (v * x) := by rw [hafix]
    have hax : a * (v * x) = v * x * a := h2.symm
    have hmem : a ∈ (nVSub V g ⊔ bSub V g) ⊓ Subgroup.centralizer ({v * x} : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hax⟩
    rw [sup_nVSub_bSub_inf_centralizer_mul_eq_bot hV hTI hvV hvD hxW hxB] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hPN : nVSub V g ⊔ bSub V g ≤ normalizer (V : Set G) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) inf_le_right
  have hPNg : nVSub V g ⊔ bSub V g ≤ normalizer (conjSubgroup V g : Set G) :=
    sup_le inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hva : ∀ a ∈ nVSub V g ⊔ bSub V g, ⁅v, a⁆ ∈ O := by
    intro a ha
    have h := O.inv_mem (hcomm a (hPN ha) v hvV)
    rwa [commutatorElement_inv] at h
  have hxa : ∀ a ∈ nVSub V g ⊔ bSub V g, ⁅x, a⁆ ∈ O := by
    intro a ha
    have haN : g * a * g⁻¹ ∈ normalizer (V : Set G) := by
      have hmem : a ∈ conjSubgroup (normalizer (V : Set G)) g := by
        rw [conjSubgroup_normalizer]
        exact hPNg ha
      exact mem_conjSubgroup_iff.mp hmem
    have hxV : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hxW
    have hmem : ⁅g * a * g⁻¹, g * x * g⁻¹⁆ ∈ O := hcomm _ haN _ hxV
    have heq : ⁅g * a * g⁻¹, g * x * g⁻¹⁆ = g * ⁅a, x⁆ * g⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [heq] at hmem
    have hmem' : ⁅a, x⁆ ∈ conjSubgroup O g := mem_conjSubgroup_iff.mpr hmem
    rw [hOg] at hmem'
    have h := O.inv_mem hmem'
    rwa [commutatorElement_inv] at h
  have hvO : ∀ o ∈ O, v * o * v⁻¹ ∈ O := by
    intro o ho
    have h := hcomm o (hOM ho) v hvV
    have heq : v * o * v⁻¹ = ⁅o, v⁆⁻¹ * o := by rw [commutatorElement_def]; group
    rw [heq]
    exact O.mul_mem (O.inv_mem h) ho
  intro p hp
  obtain ⟨a, ha, hpa⟩ :=
    w15p_core_exists_eq_commutator hcommP hyP hfix p (Subgroup.mem_sup_left hp)
  rw [hpa]
  have hvaO : v * ⁅x, a⁆ * v⁻¹ ∈ O := hvO _ (hxa a ha)
  have heq : ⁅v * x, a⁆ = (v * ⁅x, a⁆ * v⁻¹) * ⁅v, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [heq]
  exact O.mul_mem hvaO (hva a ha)

end CFSG.LocalAnalysis.WeakClosure81
