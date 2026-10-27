module

import CFSG.Quasithin.Background.D2Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

section Toolbox

variable {W : Type*} [CommGroup W]

theorem stableUnder_sup {X : Subgroup (MulAut W)} {U V : Subgroup W} (hU : StableUnder X U)
    (hV : StableUnder X V) : StableUnder X (U ⊔ V) := by
  intro x hx u hu
  rw [Subgroup.mem_sup] at hu ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  exact ⟨x a, hU x hx a ha, x b, hV x hx b hb, (map_mul x a b).symm⟩

theorem stableUnder_inf {X : Subgroup (MulAut W)} {U V : Subgroup W} (hU : StableUnder X U)
    (hV : StableUnder X V) : StableUnder X (U ⊓ V) := by
  intro x hx u hu
  exact ⟨hU x hx u hu.1, hV x hx u hu.2⟩

theorem stableUnder_iSup {ι : Sort*} {X : Subgroup (MulAut W)} {U : ι → Subgroup W}
    (hU : ∀ i, StableUnder X (U i)) : StableUnder X (⨆ i, U i) := by
  intro x hx u hu
  refine Subgroup.iSup_induction U (C := fun y => x y ∈ ⨆ i, U i) hu ?_ ?_ ?_
  · intro i y hy
    exact Subgroup.mem_iSup_of_mem i (hU i x hx y hy)
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz

theorem stableUnder_fixV {Y H : Subgroup (MulAut W)} (hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    StableUnder Y (fixV H) := by
  intro y hy w hw
  rw [mem_fixV] at hw ⊢
  intro h hh
  have hmem : y⁻¹ * h * y ∈ H := hn y⁻¹ (Y.inv_mem hy) h hh
  have hfix : (y⁻¹ * h * y) w = w := hw _ hmem
  have h1 : y⁻¹ (h (y w)) = w := by
    rw [MulAut.mul_apply, MulAut.mul_apply] at hfix
    exact hfix
  calc h (y w) = y (y⁻¹ (h (y w))) := (MulEquiv.apply_symm_apply y _).symm
    _ = y w := by rw [h1]

theorem stableUnder_commSub {H X : Subgroup (MulAut W)}
    (hn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) {M : Subgroup W} (hM : StableUnder H M) :
    StableUnder H (commSub M X) := by
  intro h hh u hu
  refine Subgroup.closure_induction (p := fun y _ => h y ∈ commSub M X) ?_ ?_ ?_ ?_ hu
  · rintro y ⟨x, hx, w, hw, rfl⟩
    refine Subgroup.subset_closure ⟨h * x * h⁻¹, hn h hh x hx, h w, hM h hh w hw, ?_⟩
    calc (h * x * h⁻¹) (h w) * (h w)⁻¹
        = h (x (h⁻¹ (h w))) * (h w)⁻¹ := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = h (x w) * (h w)⁻¹ := by rw [MulAut.inv_apply_self]
      _ = h (x w) * h (w⁻¹) := by rw [← map_inv]
      _ = h (x w * w⁻¹) := by rw [map_mul]
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z hy hz ihy ihz
    rw [map_mul]
    exact Subgroup.mul_mem _ ihy ihz
  · intro y hy ihy
    rw [map_inv]
    exact Subgroup.inv_mem _ ihy

theorem conj_mem_of_normal_subgroupOf {Y H : Subgroup (MulAut W)} (hHY : H ≤ Y)
    (hn : (H.subgroupOf Y).Normal) : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H := by
  intro y hy h hh
  have hmem : (⟨h, hHY hh⟩ : Y) ∈ H.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hh
  have hconj := hn.conj_mem (⟨h, hHY hh⟩ : Y) hmem (⟨y, hy⟩ : Y)
  exact Subgroup.mem_subgroupOf.mp hconj

theorem not_le_fixV_of_mem_irrSet {X : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : I ∈ irrSet X) : ¬ I ≤ fixV X := by
  intro h
  have hlt : I ⊓ fixV X < I := hI.2.1
  have hinf : I ⊓ fixV X = I := le_antisymm inf_le_left (le_inf le_rfl h)
  rw [hinf] at hlt
  exact lt_irrefl I hlt

theorem ne_bot_of_mem_irrSet {X : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet X) :
    I ≠ ⊥ := by
  intro hbot
  exact not_le_fixV_of_mem_irrSet hI (by rw [hbot]; exact bot_le)

theorem stableUnder_of_mem_irrSet {X : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : I ∈ irrSet X) : StableUnder X I :=
  hI.2.2.1

end Toolbox

section QuadTrivial

variable {W : Type*} [CommGroup W]

@[expose] def QuadTrivial (X : Subgroup (MulAut W)) : Prop :=
  ∀ J : Subgroup W, StableUnder X J → commSub J X ≤ fixV X → commSub J X = ⊥

theorem quadTrivial_of_commutator_eq_top {X : Subgroup (MulAut W)} (hX : commutator ↥X = ⊤) :
    QuadTrivial X := by
  intro J hJ hle
  rw [commSub_eq_bot_iff]
  intro u hu x hx
  let f : ↥X →* (↥J → W) :=
    { toFun := fun x => fun u => (x : MulAut W) u * u⁻¹
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro x y
        ext u
        have hyu : (y : MulAut W) (u : W) * (u : W)⁻¹ ∈ fixV X :=
          hle (Subgroup.subset_closure ⟨(y : MulAut W), y.2, (u : W), u.2, rfl⟩)
        have hfix : (x : MulAut W) ((y : MulAut W) (u : W) * (u : W)⁻¹)
            = (y : MulAut W) (u : W) * (u : W)⁻¹ :=
          (mem_fixV.mp hyu) x x.2
        have hsplit : (u : W) * ((y : MulAut W) (u : W) * (u : W)⁻¹)
            = (y : MulAut W) (u : W) := by
          rw [← mul_assoc, mul_comm (u : W) ((y : MulAut W) (u : W)), mul_assoc, mul_inv_cancel,
            mul_one]
        change ((x : MulAut W) * (y : MulAut W)) (u : W) * (u : W)⁻¹
            = ((x : MulAut W) (u : W) * (u : W)⁻¹) * ((y : MulAut W) (u : W) * (u : W)⁻¹)
        rw [MulAut.mul_apply]
        calc (x : MulAut W) ((y : MulAut W) (u : W)) * (u : W)⁻¹
            = (x : MulAut W) ((u : W) * ((y : MulAut W) (u : W) * (u : W)⁻¹))
                * (u : W)⁻¹ := by rw [hsplit]
          _ = ((x : MulAut W) (u : W) * ((y : MulAut W) (u : W) * (u : W)⁻¹))
                * (u : W)⁻¹ := by rw [map_mul, hfix]
          _ = ((x : MulAut W) (u : W) * (u : W)⁻¹)
                * ((y : MulAut W) (u : W) * (u : W)⁻¹) := by
                rw [mul_assoc ((x : MulAut W) (u : W)) ((y : MulAut W) (u : W) * (u : W)⁻¹)
                  (u : W)⁻¹, mul_comm ((y : MulAut W) (u : W) * (u : W)⁻¹) (u : W)⁻¹,
                  ← mul_assoc] }
  have hker : ∀ x : ↥X, f x = 1 := by
    intro x
    refine MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker f ?_)
    rw [hX]
    exact Subgroup.mem_top x
  have h1 : f ⟨x, hx⟩ = 1 := hker ⟨x, hx⟩
  have h2 : (x : MulAut W) u * u⁻¹ = 1 := by
    have h := congrArg (fun g : ↥J → W => g ⟨u, hu⟩) h1
    simpa [f] using h
  exact mul_inv_eq_one.mp h2

theorem quadTrivial_of_odd (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) : QuadTrivial X := by
  intro J hJ hle
  rw [commSub_eq_bot_iff]
  intro u hu x hx
  have hgen : x u * u⁻¹ ∈ fixV X :=
    hle (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
  set c : W := x u * u⁻¹ with hc
  have hxc : x c = c := (mem_fixV.mp hgen) x hx
  have hxu : x u = u * c := by
    rw [hc]
    calc x u = x u * (u * u⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = x u * u * u⁻¹ := by rw [mul_assoc]
      _ = u * x u * u⁻¹ := by rw [mul_comm (x u) u]
      _ = u * (x u * u⁻¹) := by rw [mul_assoc]
  have hpow : ∀ n : ℕ, (x ^ n) u = u * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hxc, hxu, pow_succ' c n]
      simp only [mul_assoc]
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)
  have hcn : c ^ orderOf x = 1 := by
    have h := hpow (orderOf x)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at h
    exact (mul_left_cancel (show u * 1 = u * c ^ orderOf x by rw [mul_one]; exact h)).symm
  obtain ⟨k, hk⟩ := hodd
  have hc1 : c = 1 := by
    rw [hk, pow_succ, show c ^ (2 * k) = (c ^ 2) ^ k from pow_mul c 2 k,
      hW c, one_pow, one_mul] at hcn
    exact hcn
  rw [hxu, hc1, mul_one]

theorem quadTrivial_iSup {ι : Sort*} {X : ι → Subgroup (MulAut W)} (hX : ∀ i, QuadTrivial (X i)) :
    QuadTrivial (⨆ i, X i) := by
  intro J hJ hle
  rw [commSub_eq_bot_iff]
  intro u hu y hy
  refine Subgroup.iSup_induction X (C := fun z => z u = u) hy ?_ ?_ ?_
  · intro i z hz
    have hJi : StableUnder (X i) J := fun w hw v hv => hJ w (le_iSup X i hw) v hv
    have hfixle : fixV (⨆ i, X i) ≤ fixV (X i) := by
      intro v hv w hw
      exact hv w (le_iSup X i hw)
    have hle_i : commSub J (X i) ≤ fixV (X i) :=
      le_trans (commSub_mono le_rfl (le_iSup X i)) (le_trans hle hfixle)
    exact (commSub_eq_bot_iff.mp (hX i J hJi hle_i)) hu z hz
  · exact MulAut.one_apply (M := W) u
  · intro a b ha hb
    rw [MulAut.mul_apply, hb, ha]

theorem quadTrivial_biSup_conj {L : Subgroup (MulAut W)} (hL : commutator ↥L = ⊤)
    (Y : Subgroup (MulAut W)) :
    QuadTrivial (⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) := by
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL
  refine quadTrivial_iSup (X := fun φ => ⨆ (_ : φ ∈ Y), L.map (MulAut.conj φ).toMonoidHom)
    (fun φ => ?_)
  refine quadTrivial_iSup (X := fun (_ : φ ∈ Y) => L.map (MulAut.conj φ).toMonoidHom) (fun _ => ?_)
  haveI : Group.IsPerfect (L.map (MulAut.conj φ).toMonoidHom) :=
    Group.IsPerfect.map (MulAut.conj φ).toMonoidHom
  exact quadTrivial_of_commutator_eq_top (Group.isPerfect_def.mp inferInstance)

end QuadTrivial

section Irr

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_mem_irrSet_le {X : Subgroup (MulAut W)} (hX : QuadTrivial X) {M : Subgroup W}
    (hM : StableUnder X M) (hne : commSub M X ≠ ⊥) : ∃ I ∈ irrSet X, I ≤ M := by
  have hnormX : ∀ y ∈ X, ∀ h ∈ X, y * h * y⁻¹ ∈ X := by
    intro y hy h hh
    exact X.mul_mem (X.mul_mem hy hh) (X.inv_mem hy)
  have hCstab : StableUnder X (fixV X) := stableUnder_fixV hnormX
  have hN₀ltM : M ⊓ fixV X < M := by
    refine lt_of_le_not_ge inf_le_left ?_
    intro hMle
    exact hne (commSub_eq_bot_iff.mpr (le_trans hMle inf_le_right))
  let cands : Set (Subgroup W) := {P | StableUnder X P ∧ M ⊓ fixV X < P ∧ P ≤ M}
  have hMmem : M ∈ cands := ⟨hM, hN₀ltM, le_rfl⟩
  obtain ⟨P, hP, hmin⟩ := (wellFounded_lt (α := Subgroup W)).has_min cands ⟨M, hMmem⟩
  obtain ⟨hPstab, hN₀ltP, hPleM⟩ := hP
  have hmin_eq : ∀ K ∈ cands, K ≤ P → K = P := by
    intro K hK hKP
    by_contra hneKP
    exact hmin K hK (lt_of_le_of_ne hKP hneKP)
  have hPinfC : P ⊓ fixV X = M ⊓ fixV X := by
    apply le_antisymm
    · exact le_inf (le_trans inf_le_left hPleM) inf_le_right
    · exact le_inf hN₀ltP.le inf_le_right
  have hIleP : commSub P X ≤ P := commSub_le_of_invariant hPstab
  have hIstab : StableUnder X (commSub P X) := stableUnder_commSub hnormX hPstab
  have hInotC : ¬ commSub P X ≤ fixV X := by
    intro hIC
    have hbot : commSub P X = ⊥ := hX P hPstab hIC
    have hPC : P ≤ fixV X := commSub_eq_bot_iff.mp hbot
    have hPinf : P ⊓ fixV X = P := le_antisymm inf_le_left (le_inf le_rfl hPC)
    have hMP : M ⊓ fixV X = P := hPinfC.symm.trans hPinf
    exact hN₀ltP.not_ge hMP.ge
  have hsupP : commSub P X ⊔ (M ⊓ fixV X) = P := by
    have hPmem : commSub P X ⊔ (M ⊓ fixV X) ∈ cands := by
      refine ⟨stableUnder_sup hIstab (stableUnder_inf hM hCstab), ?_, ?_⟩
      · refine lt_of_le_not_ge le_sup_right ?_
        intro hle
        exact hInotC ((le_trans le_sup_left hle).trans inf_le_right)
      · exact sup_le (hIleP.trans hPleM) inf_le_left
    exact hmin_eq _ hPmem (sup_le hIleP hN₀ltP.le)
  have hcommI : commSub (commSub P X) X = commSub P X := by
    have hbot : commSub (M ⊓ fixV X) X = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
    have h2 : commSub (commSub P X ⊔ (M ⊓ fixV X)) X = commSub P X := by rw [hsupP]
    rw [commSub_sup_left, hbot, sup_bot_eq] at h2
    exact h2
  have hltI : commSub P X ⊓ fixV X < commSub P X := by
    refine lt_of_le_not_ge inf_le_left ?_
    intro hle
    exact hInotC (le_trans hle inf_le_right)
  have hinfstab : StableUnder X (commSub P X ⊓ fixV X) := stableUnder_inf hIstab hCstab
  have hirr : ∀ K : Subgroup W, StableUnder X K → commSub P X ⊓ fixV X ≤ K →
      K ≤ commSub P X → K = commSub P X ⊓ fixV X ∨ K = commSub P X := by
    intro K hKstab hIK hKI
    have hKsup_le_P : K ⊔ (M ⊓ fixV X) ≤ P := sup_le (hKI.trans hIleP) hN₀ltP.le
    rcases eq_or_lt_of_le (le_sup_right : M ⊓ fixV X ≤ K ⊔ (M ⊓ fixV X)) with hcase | hcase
    · left
      apply le_antisymm ?_ hIK
      exact le_inf hKI ((le_trans le_sup_left (le_of_eq hcase.symm)).trans inf_le_right)
    · right
      have hsup_mem : K ⊔ (M ⊓ fixV X) ∈ cands :=
        ⟨stableUnder_sup hKstab (stableUnder_inf hM hCstab), hcase, hKsup_le_P.trans hPleM⟩
      have hsupP' : K ⊔ (M ⊓ fixV X) = P := hmin_eq _ hsup_mem hKsup_le_P
      have hIleK : commSub P X ≤ K := by
        have hbot : commSub (M ⊓ fixV X) X = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
        have hmono : commSub (commSub P X) X ≤ commSub (K ⊔ (M ⊓ fixV X)) X :=
          commSub_mono (hIleP.trans hsupP'.ge) le_rfl
        rw [hcommI, commSub_sup_left, hbot, sup_bot_eq] at hmono
        exact hmono.trans (commSub_le_of_invariant hKstab)
      exact le_antisymm hKI hIleK
  refine ⟨commSub P X, ?_, hIleP.trans hPleM⟩
  refine ⟨hcommI, ?_⟩
  exact ⟨hltI, hIstab, hinfstab, hirr⟩

end Irr

end CFSG.LocalAnalysis.WeakClosure81
