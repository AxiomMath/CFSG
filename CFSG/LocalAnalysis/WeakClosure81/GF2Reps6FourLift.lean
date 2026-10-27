module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24 (eq_top_of_mul_center)
open scoped commutatorElement

private theorem exists_conj_fixed_lift {P : Type*} [Group P] {L A : Subgroup P}
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) {a : P} (haA : a ∈ A) (ha : a * a = 1)
    (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    {β : MulAut (↥L ⧸ Subgroup.center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    {y : ↥L ⧸ Subgroup.center ↥L} (hy : β y = y) :
    ∃ c : ↥L, (QuotientGroup.mk c : ↥L ⧸ Subgroup.center ↥L) = y ∧
      a * (c : P) * a⁻¹ = (c : P) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  let x : ↥L := ⟨a * (l : P) * a⁻¹, hAL a haA l l.2⟩
  have hπ : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l :=
    (hβ l).symm.trans hy
  have hζZ : l⁻¹ * x ∈ Subgroup.center ↥L := QuotientGroup.eq.mp hπ.symm
  set ζ : ↥L := l⁻¹ * x with hζdef
  have hxl : x = l * ζ := by
    rw [hζdef]
    group
  have hζn : ζ ^ Nat.card (Subgroup.center ↥L) = 1 := by
    have hpow : (⟨ζ, hζZ⟩ : Subgroup.center ↥L) ^ Nat.card (Subgroup.center ↥L) = 1 :=
      pow_card_eq_one'
    have hval : ((⟨ζ, hζZ⟩ : Subgroup.center ↥L) : ↥L) ^
        Nat.card (Subgroup.center ↥L) = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hpow
    exact hval
  obtain ⟨m, hm⟩ := hZ
  have hx2 : ζ ^ (m + 1) * ζ ^ (m + 1) = ζ := by
    rw [← pow_add]
    have h2 : m + 1 + (m + 1) = Nat.card (Subgroup.center ↥L) + 1 := by
      rw [hm]
      ring
    rw [h2, pow_succ, hζn, one_mul]
  have hφL : MulAut.conj a (l : P) = (l : P) * (ζ : P) := by
    rw [MulAut.conj_apply]
    have h := congrArg Subtype.val hxl
    simpa only [x, Subgroup.coe_mul] using h
  have hφ2 : MulAut.conj a * MulAut.conj a = 1 := by
    rw [← map_mul, ha, map_one]
  have hφφ : MulAut.conj a (MulAut.conj a (l : P)) = (l : P) := by
    have h : (MulAut.conj a * MulAut.conj a) (l : P) = (l : P) := by
      rw [hφ2]
      rfl
    simpa using h
  have hmain : (l : P) = (l : P) * (ζ : P) * MulAut.conj a (ζ : P) := by
    calc (l : P) = MulAut.conj a (MulAut.conj a (l : P)) := hφφ.symm
      _ = MulAut.conj a ((l : P) * (ζ : P)) := by rw [hφL]
      _ = MulAut.conj a (l : P) * MulAut.conj a (ζ : P) := map_mul _ _ _
      _ = ((l : P) * (ζ : P)) * MulAut.conj a (ζ : P) := by rw [hφL]
  have hcancel : (ζ : P) * MulAut.conj a (ζ : P) = 1 := by
    have h := congrArg (fun t : P => (l : P)⁻¹ * t) hmain
    rw [show (l : P)⁻¹ * ((l : P) * (ζ : P) * MulAut.conj a (ζ : P)) =
        (ζ : P) * MulAut.conj a (ζ : P) by group,
      show (l : P)⁻¹ * (l : P) = 1 by group] at h
    exact h.symm
  have hζinv : MulAut.conj a (ζ : P) = (ζ : P)⁻¹ :=
    eq_inv_of_mul_eq_one_right hcancel
  refine ⟨l * ζ ^ (m + 1), ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff ζ).mpr hζZ, one_pow, mul_one]
  · set xp : P := (ζ : P) ^ (m + 1) with hxp
    have hx2P : xp * xp = (ζ : P) := by
      have h := congrArg Subtype.val hx2
      simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h
      rwa [← hxp] at h
    have hxinvP : xp⁻¹ = xp * (ζ : P)⁻¹ := by
      rw [← hx2P]
      group
    have hconj_xp : MulAut.conj a xp = xp⁻¹ := by
      rw [hxp, map_pow, hζinv, inv_pow]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [← MulAut.conj_apply]
    calc MulAut.conj a ((l : P) * xp)
        = MulAut.conj a (l : P) * MulAut.conj a xp := map_mul _ _ _
      _ = ((l : P) * (ζ : P)) * xp⁻¹ := by rw [hφL, hconj_xp]
      _ = (l : P) * xp := by
          rw [hxinvP, ← hx2P]
          group

private theorem comm_mem_quadY {P : Type*} [Group P] {L A : Subgroup P}
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) {a : P}
    {c : ↥L} (hc : a * (c : P) * a⁻¹ = (c : P)) {u : P} (hu : u ∈ A) :
    ((c : P) * u * (c : P)⁻¹ * u⁻¹ ∈ L) ∧
      ((c : P) * u * (c : P)⁻¹ * u⁻¹ ∈ quadY L A a) := by
  have hca : (c : P) * a = a * (c : P) := by
    calc (c : P) * a = (a * (c : P) * a⁻¹) * a := by rw [hc]
      _ = a * (c : P) := by group
  have huL : u * (c : P)⁻¹ * u⁻¹ ∈ L := by
    simpa using hAL u hu c⁻¹ c⁻¹.2
  have hcu : (c : P) * u * (c : P)⁻¹ ∈ quadY L A a := by
    refine Subgroup.mem_iSup_of_mem (c : P) (Subgroup.mem_iSup_of_mem c.2
      (Subgroup.mem_iSup_of_mem hca ?_))
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_map_of_mem (MulAut.conj (c : P)).toMonoidHom hu)
  have huinv : u⁻¹ ∈ quadY L A a := by
    have hA : A ≤ quadY L A a := by
      intro y hy
      refine Subgroup.mem_iSup_of_mem (1 : P) (Subgroup.mem_iSup_of_mem L.one_mem
        (Subgroup.mem_iSup_of_mem (by simp) ?_))
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_map_of_mem (MulAut.conj (1 : P)).toMonoidHom hy)
    exact hA (A.inv_mem hu)
  constructor
  · have h := L.mul_mem c.2 huL
    simpa [mul_assoc] using h
  · have h := (quadY L A a).mul_mem hcu huinv
    simpa [mul_assoc] using h

theorem le_quadY_sup_conj_of_commY {P : Type*} [Group P] {L A : Subgroup P}
    (hL : commutator ↥L = ⊤) (hZ : Odd (Nat.card (center ↥L)))
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) {a : P} (haA : a ∈ A) (ha : a * a = 1)
    {B : Subgroup (MulAut (↥L ⧸ center ↥L))} {β : MulAut (↥L ⧸ center ↥L)}
    (hβ : ∀ l : ↥L, β (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨a * l * a⁻¹, hAL a haA l l.2⟩ : ↥L))
    (hB : ∀ b ∈ B, ∃ u, ∃ hu : u ∈ A, ∀ l : ↥L, b (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨u * l * u⁻¹, hAL u hu l l.2⟩ : ↥L))
    {k : ↥L} (hgen : commY B β ⊔ (commY B β).map
      (MulAut.conj (QuotientGroup.mk k : ↥L ⧸ center ↥L)).toMonoidHom = ⊤) :
    L ≤ quadY L A a ⊔ (quadY L A a).map (MulAut.conj (k : P)).toMonoidHom := by
  let M : Subgroup P := quadY L A a ⊔ (quadY L A a).map (MulAut.conj (k : P)).toMonoidHom
  let ML : Subgroup ↥L := M.subgroupOf L
  let N : Subgroup (↥L ⧸ center ↥L) := ML.map (QuotientGroup.mk' (center ↥L))
  have hcomm_le : commY B β ≤ N := by
    unfold commY
    refine (Subgroup.closure_le N).mpr ?_
    rintro w ⟨y, hy, b, hb, rfl⟩
    obtain ⟨c, hcy, hca⟩ := exists_conj_fixed_lift hAL haA ha hZ hβ hy
    obtain ⟨u, hu, hbu⟩ := hB b hb
    have hby : b y = QuotientGroup.mk (⟨u * c * u⁻¹, hAL u hu c c.2⟩ : ↥L) := by
      rw [← hcy]
      exact hbu c
    obtain ⟨hwL, hwY⟩ := comm_mem_quadY hAL hca hu
    refine Subgroup.mem_map.mpr ⟨⟨(c : P) * u * (c : P)⁻¹ * u⁻¹, hwL⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hwY)
    · rw [QuotientGroup.mk'_apply, hby, ← hcy]
      have hsub : (⟨(c : P) * u * (c : P)⁻¹ * u⁻¹, hwL⟩ : ↥L) =
          c * (⟨u * c * u⁻¹, hAL u hu c c.2⟩ : ↥L)⁻¹ := by
        apply Subtype.ext
        show (c : P) * u * (c : P)⁻¹ * u⁻¹ = (c : P) * (u * (c : P) * u⁻¹)⁻¹
        group
      rw [hsub, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmap_le : (commY B β).map
      (MulAut.conj (QuotientGroup.mk k : ↥L ⧸ center ↥L)).toMonoidHom ≤ N := by
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    unfold commY
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨y, hy, b, hb, rfl⟩
    change (MulAut.conj (QuotientGroup.mk k : ↥L ⧸ center ↥L)) (y * (b y)⁻¹) ∈ N
    obtain ⟨c, hcy, hca⟩ := exists_conj_fixed_lift hAL haA ha hZ hβ hy
    obtain ⟨u, hu, hbu⟩ := hB b hb
    have hby : b y = QuotientGroup.mk (⟨u * c * u⁻¹, hAL u hu c c.2⟩ : ↥L) := by
      rw [← hcy]
      exact hbu c
    obtain ⟨hwL, hwY⟩ := comm_mem_quadY hAL hca hu
    have hkL : (k : P) * ((c : P) * u * (c : P)⁻¹ * u⁻¹) * (k : P)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem k.2 hwL) (L.inv_mem k.2)
    have hz : y * (b y)⁻¹ =
        QuotientGroup.mk (⟨(c : P) * u * (c : P)⁻¹ * u⁻¹, hwL⟩ : ↥L) := by
      rw [hby, ← hcy, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (c : P) * (u * (c : P) * u⁻¹)⁻¹ = (c : P) * u * (c : P)⁻¹ * u⁻¹
      group
    have hfz : (MulAut.conj (QuotientGroup.mk k : ↥L ⧸ center ↥L))
        (y * (b y)⁻¹) =
        QuotientGroup.mk
          (⟨(k : P) * ((c : P) * u * (c : P)⁻¹ * u⁻¹) * (k : P)⁻¹, hkL⟩ : ↥L) := by
      rw [hz, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
    refine Subgroup.mem_map.mpr
      ⟨⟨(k : P) * ((c : P) * u * (c : P)⁻¹ * u⁻¹) * (k : P)⁻¹, hkL⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ?_)
      exact Subgroup.mem_map.mpr
        ⟨_, hwY, MulAut.conj_apply (k : P) ((c : P) * u * (c : P)⁻¹ * u⁻¹)⟩
    · rw [QuotientGroup.mk'_apply]
      exact hfz.symm
  have hNtop : N = ⊤ := by
    refine le_antisymm le_top ?_
    have hle : commY B β ⊔ (commY B β).map
        (MulAut.conj (QuotientGroup.mk k : ↥L ⧸ center ↥L)).toMonoidHom ≤ N :=
      sup_le hcomm_le hmap_le
    rwa [hgen] at hle
  have htop : (⊤ : Subgroup ↥L) ≤ ML ⊔ center ↥L := by
    intro l _
    have hlN : (QuotientGroup.mk l : ↥L ⧸ center ↥L) ∈
        ML.map (QuotientGroup.mk' (center ↥L)) := by
      have h : (QuotientGroup.mk l : ↥L ⧸ center ↥L) ∈ N := by
        rw [hNtop]
        exact Subgroup.mem_top _
      exact h
    obtain ⟨m, hmML, hmk⟩ := Subgroup.mem_map.mp hlN
    have hml : (QuotientGroup.mk m : ↥L ⧸ center ↥L) = QuotientGroup.mk l := by
      rw [← QuotientGroup.mk'_apply (N := center ↥L) m]
      exact hmk
    have hcenter : m⁻¹ * l ∈ center ↥L := by
      refine (QuotientGroup.eq_one_iff (m⁻¹ * l)).mp ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hml]
      exact inv_mul_cancel _
    have hl : l = m * (m⁻¹ * l) := by group
    rw [hl]
    exact (ML ⊔ center ↥L).mul_mem (Subgroup.mem_sup_left hmML)
      (Subgroup.mem_sup_right hcenter)
  have hMLtop : ML = ⊤ := eq_top_of_mul_center hL fun l => by
    obtain ⟨y, hy, z, hz, h⟩ := Subgroup.mem_sup_of_normal_right.1 (htop (Subgroup.mem_top l))
    exact ⟨y, hy, z, hz, h.symm⟩
  exact Subgroup.subgroupOf_eq_top.mp hMLtop

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
