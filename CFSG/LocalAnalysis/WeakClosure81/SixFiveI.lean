module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem conjSubgroup_N_eq (h : Hyp65 n M V₀ V g) {x : G} (hx : x ∈ LOf V g) :
    conjSubgroup (NOf M V g) x = NOf M V g := by
  have hcopy := h
  apply le_antisymm
  · intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hc := N_le_centralizer_L hcopy hy
    have hcomm := Subgroup.mem_centralizer_iff.1 hc x hx
    have hEq : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
      calc x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [← hcomm]
        _ = x * y * x⁻¹ := by group
    have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [hy', hEq]
    exact hy
  · intro n hn
    rw [mem_conjSubgroup_iff]
    have hc := N_le_centralizer_L hcopy hn
    have hcomm := Subgroup.mem_centralizer_iff.1 hc x hx
    rwa [show x * n * x⁻¹ = n by rw [hcomm]; group]

theorem not_B_le_U (h : Hyp65 n M V₀ V g) : ¬ BOf M V g ≤ UOf M V g := by
  intro hBU
  have hYV : YOf M V₀ g ≤ V :=
    (Y_le_B h).trans (hBU.trans (show UOf M V g ≤ V by rw [UOf]; exact inf_le_left))
  have hYV0g : YOf M V₀ g ≤ conjSubgroup V₀ g := by rw [YOf]; exact inf_le_left
  have hbot : YOf M V₀ g ≤ (⊥ : Subgroup G) := by
    rw [← conjV₀_inf_V h]
    exact le_inf hYV0g hYV
  exact Y_ne_bot h (le_bot_iff.1 hbot)

theorem conjSubgroup_U_eq_B_of_swap (h : Hyp65 n M V₀ V g) {l : G}
    (h1 : conjSubgroup V l = conjSubgroup V g) (h2 : conjSubgroup (conjSubgroup V g) l = V) :
    conjSubgroup (UOf M V g) l = BOf M V g := by
  have hMg : conjSubgroup M g = normalizer (conjSubgroup V g : Set G) := by
    rw [← h.normalizer_eq, conjSubgroup_normalizer]
  have hMl : conjSubgroup (conjSubgroup M g) l = M := by
    rw [hMg, conjSubgroup_normalizer, h2, h.normalizer_eq]
  unfold UOf BOf
  rw [conjSubgroup_inf, h1, hMl]

theorem U_centralizesMod_le_N (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) {x : G}
    (hxVg : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    ∀ u ∈ UOf M V g, ⁅u, x⁆ ∈ NOf M V g → u ∈ NOf M V g := by
  have hcopy := h
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  have hUL : UOf M V g ≤ LOf V g := fun u hu => Subgroup.mem_sup_left hu.1
  have hxL : x ∈ LOf V g := Subgroup.mem_sup_right hxVg
  have hK_eq : KOf M V g = UOf M V g ⊔ BOf M V g := rfl
  have hKnorm_L : LOf V g ≤ normalizer (KOf M V g : Set G) := L_le_normalizer_K h
  have hx_notK : x ∉ UOf M V g ⊔ BOf M V g := by
    intro hxK
    apply hxB
    have hmem : x ∈ conjSubgroup V g ⊓ KOf M V g := ⟨hxVg, hxK⟩
    rwa [conjV_inf_K h] at hmem
  let S : Subgroup G :=
    { carrier := {u | u ∈ UOf M V g ∧ ⁅u, x⁆ ∈ NOf M V g}
      mul_mem' := by
        rintro u w ⟨huU, huN⟩ ⟨hwU, hwN⟩
        refine ⟨(UOf M V g).mul_mem huU hwU, ?_⟩
        have hw : u * ⁅w, x⁆ * u⁻¹ = ⁅w, x⁆ := by
          have hcommu :=
            Subgroup.mem_centralizer_iff.1 (N_le_centralizer_L hcopy hwN) u (hUL huU)
          rw [hcommu]; group
        rw [commutatorElement_mul_left_eq_conj_mul, hw]
        exact (NOf M V g).mul_mem hwN huN
      one_mem' := ⟨(UOf M V g).one_mem, by simp⟩
      inv_mem' := by
        rintro u ⟨huU, huN⟩
        refine ⟨(UOf M V g).inv_mem huU, ?_⟩
        rw [commutatorElement_inv_left]
        have hcommu := Subgroup.mem_centralizer_iff.1
          (N_le_centralizer_L hcopy ((NOf M V g).inv_mem huN)) u (hUL huU)
        have hxu : ⁅x, u⁆ = ⁅u, x⁆⁻¹ := (commutatorElement_inv u x).symm
        have hEq : u⁻¹ * ⁅u, x⁆⁻¹ * u = ⁅u, x⁆⁻¹ := by
          calc u⁻¹ * ⁅u, x⁆⁻¹ * u = u⁻¹ * (⁅u, x⁆⁻¹ * u) := by group
            _ = u⁻¹ * (u * ⁅u, x⁆⁻¹) := by rw [← hcommu]
            _ = ⁅u, x⁆⁻¹ := by group
        rw [hxu, hEq]
        exact (NOf M V g).inv_mem huN }
  have hNS : NOf M V g ≤ S := by
    intro n hn
    refine ⟨(Subgroup.mem_inf.1 hn).1, ?_⟩
    rw [NOf_eq M V g h.le_M] at hn
    have hnVg : n ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hn).2
    have hn2 : n * x = x * n := IsElemAbelian.comm hVgel hnVg hxVg
    have h1 : ⁅n, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hn2
    rw [h1]
    exact (NOf M V g).one_mem
  let C : Subgroup G :=
    { carrier := {y | y ∈ LOf V g ∧ ∀ s ∈ S, ⁅s, y⁆ ∈ NOf M V g}
      mul_mem' := by
        rintro y z ⟨hyL, hyN⟩ ⟨hzL, hzN⟩
        refine ⟨(LOf V g).mul_mem hyL hzL, ?_⟩
        intro s hs
        have hz : y * ⁅s, z⁆ * y⁻¹ = ⁅s, z⁆ := by
          have hcommy :=
            Subgroup.mem_centralizer_iff.1 (N_le_centralizer_L hcopy (hzN s hs)) y hyL
          rw [hcommy]; group
        have hyz : ⁅s, y⁆ * y * ⁅s, z⁆ * y⁻¹ = ⁅s, y⁆ * ⁅s, z⁆ := by
          calc ⁅s, y⁆ * y * ⁅s, z⁆ * y⁻¹ = ⁅s, y⁆ * (y * ⁅s, z⁆ * y⁻¹) := by group
            _ = ⁅s, y⁆ * ⁅s, z⁆ := by rw [hz]
        rw [commutatorElement_mul_right_eq_mul_conj, hyz]
        exact (NOf M V g).mul_mem (hyN s hs) (hzN s hs)
      one_mem' := ⟨(LOf V g).one_mem, by intro s hs; simp⟩
      inv_mem' := by
        rintro y ⟨hyL, hyN⟩
        refine ⟨(LOf V g).inv_mem hyL, ?_⟩
        intro s hs
        rw [commutatorElement_inv_right]
        have hyu : ⁅y, s⁆ = ⁅s, y⁆⁻¹ := (commutatorElement_inv s y).symm
        rw [hyu]
        have hcommy := Subgroup.mem_centralizer_iff.1
          (N_le_centralizer_L hcopy ((NOf M V g).inv_mem (hyN s hs))) y⁻¹
          ((LOf V g).inv_mem hyL)
        have hEq : y⁻¹ * ⁅s, y⁆⁻¹ * y = ⁅s, y⁆⁻¹ := by rw [hcommy]; group
        rw [hEq]
        exact (NOf M V g).inv_mem (hyN s hs) }
  have hVC : V ≤ C := by
    intro v hv
    refine ⟨Subgroup.mem_sup_left hv, ?_⟩
    intro s hs
    have h1 : ⁅s, v⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hs.1.1 hv)
    rw [h1]
    exact (NOf M V g).one_mem
  have hxC : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.2 ⟨hxL, fun s hs => hs.2⟩
  have hUC : UOf M V g ≤ C := by
    intro u hu
    refine ⟨hUL hu, ?_⟩
    intro s hs
    have h1 : ⁅s, u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hs.1.1 hu.1)
    rw [h1]
    exact (NOf M V g).one_mem
  have hBC : BOf M V g ≤ C := by
    intro b hb
    refine ⟨Subgroup.mem_sup_right hb.1, ?_⟩
    intro s hs
    exact commutator_U_B_le_N hcopy (Subgroup.commutator_mem_commutator hs.1 hb)
  have hsupC : (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g) ≤ C :=
    sup_le (sup_le hVC hxC) (sup_le hUC hBC)
  have hLC : LOf V g ≤ C := (hgen x hxVg hx_notK).trans hsupC
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hlV' : conjSubgroup V l = conjSubgroup V g := hlV.symm
  have hlC := hLC hlL
  have hconjS_le_S : conjSubgroup S l ≤ S := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    obtain ⟨s, hs, hs_eq⟩ : ∃ s ∈ S, l⁻¹ * s * l = y := ⟨l * y * l⁻¹, hy, by group⟩
    rw [← hs_eq]
    have hsl : ⁅s, l⁆ ∈ NOf M V g := hlC.2 s hs
    have hcomml := Subgroup.mem_centralizer_iff.1 (N_le_centralizer_L hcopy hsl) l hlL
    have hEq : l⁻¹ * s * l = (l⁻¹ * ⁅s, l⁆ * l) * s := by
      rw [commutatorElement_def]; group
    rw [hEq]
    have hNl : l⁻¹ * ⁅s, l⁆ * l = ⁅s, l⁆ := by
      calc l⁻¹ * ⁅s, l⁆ * l = l⁻¹ * (⁅s, l⁆ * l) := by group
        _ = l⁻¹ * (l * ⁅s, l⁆) := by rw [← hcomml]
        _ = ⁅s, l⁆ := by group
    rw [hNl]
    exact S.mul_mem (hNS hsl) hs
  have hconjS_le_B : conjSubgroup S l ≤ BOf M V g := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    obtain ⟨s, hs, hs_eq⟩ : ∃ s ∈ S, l⁻¹ * s * l = y := ⟨l * y * l⁻¹, hy, by group⟩
    rw [← hs_eq]
    have hVg : l⁻¹ * s * l ∈ conjSubgroup V g := by
      have hmem : l⁻¹ * s * l ∈ conjSubgroup (UOf M V g) l := by
        rw [mem_conjSubgroup_iff]
        rw [show l * (l⁻¹ * s * l) * l⁻¹ = s by group]
        exact hs.1
      exact hlV' ▸ conjSubgroup_mono (fun u (hu : u ∈ UOf M V g) => hu.1) l hmem
    have hK : l⁻¹ * s * l ∈ KOf M V g := by
      have hsK : s ∈ KOf M V g := by rw [hK_eq]; exact Subgroup.mem_sup_left hs.1
      have hmem : l⁻¹ * s * l ∈ conjSubgroup (KOf M V g) l := by
        rw [mem_conjSubgroup_iff]
        rw [show l * (l⁻¹ * s * l) * l⁻¹ = s by group]
        exact hsK
      rwa [conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hlL)] at hmem
    have hy' : l⁻¹ * s * l ∈ conjSubgroup V g ⊓ KOf M V g := ⟨hVg, hK⟩
    rwa [conjV_inf_K h] at hy'
  have hS_le_N : S ≤ NOf M V g := by
    have hconjS_le_N : conjSubgroup S l ≤ NOf M V g :=
      le_inf (hconjS_le_S.trans (fun s hs => hs.1)) hconjS_le_B
    have hmono : conjSubgroup (conjSubgroup S l) l⁻¹ ≤ conjSubgroup (NOf M V g) l⁻¹ :=
      conjSubgroup_mono hconjS_le_N l⁻¹
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
      conjSubgroup_N_eq hcopy ((LOf V g).inv_mem hlL)] at hmono
    exact hmono
  intro u hu huN
  exact hS_le_N ⟨hu, huN⟩

theorem stepA (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) {x : G}
    (hxVg : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    ∀ k ∈ KOf M V g, ⁅k, x⁆ ∈ NOf M V g → k ∈ BOf M V g := by
  have hcopy := h
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using
      IsElemAbelian.map h.elemAbelian (MulAut.conj g⁻¹).toMonoidHom
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N hcopy).trans inf_le_right
  intro k hkK hkN
  change k ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) at hkK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hkK
  obtain ⟨u, huU, b, hbB, rfl⟩ := hkK
  have hux : ⁅u, x⁆ ∈ NOf M V g := by
    have hbx : ⁅b, x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hVgel hbB.1 hxVg)
    have : u * ⁅b, x⁆ * u⁻¹ * ⁅u, x⁆ = ⁅u, x⁆ := by rw [hbx]; group
    rwa [commutatorElement_mul_left_eq_conj_mul, this] at hkN
  have huN : u ∈ NOf M V g := U_centralizesMod_le_N h hgen hlK hxVg hxB u huU hux
  exact (BOf M V g).mul_mem ((Subgroup.mem_inf.1 huN).2) hbB

theorem stepB (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) {v : G}
    (hvV : v ∈ V) (hvU : v ∉ UOf M V g) :
    ∀ k ∈ KOf M V g, ⁅k, v⁆ ∈ NOf M V g → k ∈ UOf M V g := by
  have hcopy := h
  have hlk := hlK
  obtain ⟨l, hlL, hlV⟩ := hlk
  have hlV' : conjSubgroup V l = conjSubgroup V g := hlV.symm
  set x : G := l⁻¹ * v * l with hxdef
  have hxVg : x ∈ conjSubgroup V g := by
    rw [← hlV', mem_conjSubgroup_iff]
    rw [show l * x * l⁻¹ = v by rw [hxdef]; group]
    exact hvV
  have hgl : g * l⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    rw [show g * l⁻¹ = (l * g⁻¹)⁻¹ by group]
    refine (Subgroup.normalizer (V : Set G)).inv_mem ?_
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hlV',
      conjSubgroup_conjSubgroup_inv]
  have hKl : conjSubgroup (KOf M V g) l⁻¹ = KOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (L_le_normalizer_K h ((LOf V g).inv_mem hlL))
  have hBK : BOf M V g = conjSubgroup V g ⊓ KOf M V g := (conjV_inf_K h).symm
  have hBl : conjSubgroup (BOf M V g) l⁻¹ = UOf M V g := by
    rw [hBK, conjSubgroup_inf, conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.2 hgl, hKl]
    exact V_inf_K h
  have hx_notB : x ∉ BOf M V g := by
    intro hxB
    apply hvU
    have hmem : l * x * l⁻¹ ∈ conjSubgroup (BOf M V g) l⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rw [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group]
      exact hxB
    rw [hBl] at hmem
    rwa [show l * x * l⁻¹ = v by rw [hxdef]; group] at hmem
  intro k hkK hkN
  set k' : G := l⁻¹ * k * l with hk'def
  have hk'_K : k' ∈ KOf M V g := by
    have hmem : k' ∈ conjSubgroup (KOf M V g) l := by
      rw [mem_conjSubgroup_iff]
      rw [show l * k' * l⁻¹ = k by rw [hk'def]; group]
      exact hkK
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 (L_le_normalizer_K h hlL)] at hmem
  have hk'x : ⁅k', x⁆ ∈ NOf M V g := by
    have hconj : l * ⁅k', x⁆ * l⁻¹ = ⁅k, v⁆ := by
      have h1 : l * k' * l⁻¹ = k := by rw [hk'def]; group
      have h2 : l * x * l⁻¹ = v := by rw [hxdef]; group
      have hcc := conjugate_commutatorElement k' x l
      rwa [h1, h2] at hcc
    have hmem : l * ⁅k', x⁆ * l⁻¹ ∈ NOf M V g := by rw [hconj]; exact hkN
    have hc := N_le_centralizer_L hcopy hmem
    have hcomml := Subgroup.mem_centralizer_iff.1 hc l hlL
    have hEq : ⁅k', x⁆ = l * ⁅k', x⁆ * l⁻¹ := by
      calc ⁅k', x⁆ = l⁻¹ * (l * ⁅k', x⁆ * l⁻¹) * l := by group
        _ = l⁻¹ * ((l * ⁅k', x⁆ * l⁻¹) * l) := by group
        _ = l⁻¹ * (l * (l * ⁅k', x⁆ * l⁻¹)) := by rw [← hcomml]
        _ = l * ⁅k', x⁆ * l⁻¹ := by group
    rwa [hEq]
  have hk'B : k' ∈ BOf M V g := stepA h hgen hlK hxVg hx_notB k' hk'_K hk'x
  have hkilB : k ∈ conjSubgroup (BOf M V g) l⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rw [show (l⁻¹) * k * (l⁻¹)⁻¹ = k' by rw [hk'def]; group]
    exact hk'B
  rwa [hBl] at hkilB

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
