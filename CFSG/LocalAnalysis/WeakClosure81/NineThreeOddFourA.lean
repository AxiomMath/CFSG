module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFrame
public import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement symmDiff

variable {Γ : Type} [Group Γ] [Finite Γ] {p m : ℕ} {π : Γ →* Equiv.Perm (ZMod p)} {D : Set Γ}

private lemma nine3_zmodRefl_mul (c a : ZMod p) :
    zmodRefl p c * zmodRefl p a * zmodRefl p c = zmodRefl p (2 * c - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private lemma nine3_zmodRefl_sq (c : ZMod p) : zmodRefl p c * zmodRefl p c = 1 := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.coe_one, id_eq]
  ring

private lemma nine3_zmodRefl_inv (c : ZMod p) : (zmodRefl p c)⁻¹ = zmodRefl p c := by
  have h2 : zmodRefl p c * zmodRefl p c = 1 := nine3_zmodRefl_sq c
  calc (zmodRefl p c)⁻¹ = (zmodRefl p c)⁻¹ * 1 := (mul_one _).symm
    _ = (zmodRefl p c)⁻¹ * (zmodRefl p c * zmodRefl p c) := by rw [h2]
    _ = ((zmodRefl p c)⁻¹ * zmodRefl p c) * zmodRefl p c := by rw [mul_assoc]
    _ = 1 * zmodRefl p c := by rw [inv_mul_cancel]
    _ = zmodRefl p c := one_mul _

private lemma nine3_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hp.two_le)

private lemma nine3_zmodRefl_ne_one (hp : p.Prime) (hp2 : p ≠ 2) (c : ZMod p) :
    zmodRefl p c ≠ 1 := by
  intro h
  have h0 : (2 : ZMod p) * c = 0 := by
    have := congrArg (fun e : Equiv.Perm (ZMod p) => e 0) h
    simpa [zmodRefl, Equiv.subLeft] using this
  have h1 : (2 : ZMod p) * c = 2 := by
    have := congrArg (fun e : Equiv.Perm (ZMod p) => e 1) h
    have h1' : (2 : ZMod p) * c - 1 = 1 := by simpa [zmodRefl, Equiv.subLeft] using this
    calc (2 : ZMod p) * c = ((2 : ZMod p) * c - 1) + 1 := (sub_add_cancel _ _).symm
      _ = 1 + 1 := by rw [h1']
      _ = 2 := by norm_num
  exact nine3_two_ne_zero hp hp2 (by rw [← h1, h0])

private lemma nine3_conj_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {a c : ZMod p} {d e : Γ}
    (hd : d ∈ D) (hda : π d = zmodRefl p a) (he : e ∈ D) (hec : π e = zmodRefl p c) :
    e * d * e⁻¹ ∈ nine3FibreSet π D (2 * c - a) := by
  refine ⟨h.conj d hd e, ?_⟩
  rw [map_mul, map_mul, map_inv, hda, hec, nine3_zmodRefl_inv]
  exact nine3_zmodRefl_mul c a

private lemma nine3_closure_commute {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p} {w d : Γ}
    (hw : w ∈ Subgroup.closure (nine3FibreSet π D c)) (hd : d ∈ nine3FibreSet π D c) :
    Commute d w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact h.comm d hd.1 x hx.1 (hd.2.trans hx.2.symm)
  | one => exact Commute.one_right d
  | mul a b _ _ iha ihb => exact iha.mul_right ihb
  | inv a _ iha => exact iha.inv_right

theorem nine3OddFrame_closure_two (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p m π D)
    {r s : ZMod p} (hrs : r ≠ s) :
    Subgroup.closure (nine3FibreSet π D r ∪ nine3FibreSet π D s) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let F : ZMod p → Set Γ := nine3FibreSet π D
  let T : Subgroup Γ := Subgroup.closure (F r ∪ F s)
  have hcardF : ∀ a : ZMod p, Nat.card ↥(F a) = m := fun a => h.card a
  have hFrT : F r ⊆ T := fun _ hx => Subgroup.subset_closure (Set.mem_union_left _ hx)
  have hFsT : F s ⊆ T := fun _ hx => Subgroup.subset_closure (Set.mem_union_right _ hx)
  have hFs_le : Subgroup.closure (F s) ≤ T := (Subgroup.closure_le T).mpr hFsT
  have hreach : 0 < m → ∀ c : ZMod p, (F c ∩ T).Nonempty := by
    intro hm c
    have hFr_ne : (F r).Nonempty := by
      have hpos : 0 < Nat.card ↥(F r) := by rw [hcardF r]; exact hm
      exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
    have hFs_ne : (F s).Nonempty := by
      have hpos : 0 < Nat.card ↥(F s) := by rw [hcardF s]; exact hm
      exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
    let L : Set (ZMod p) := {a | (F a ∩ T).Nonempty}
    have hrL : r ∈ L := by
      obtain ⟨d, hd⟩ := hFr_ne
      exact ⟨d, hd, hFrT hd⟩
    have hsL : s ∈ L := by
      obtain ⟨d, hd⟩ := hFs_ne
      exact ⟨d, hd, hFsT hd⟩
    have hconj : ∀ {a c : ZMod p}, a ∈ L → c ∈ L → 2 * c - a ∈ L := by
      rintro a c ⟨d, hdF, hdT⟩ ⟨e, heF, heT⟩
      exact ⟨e * d * e⁻¹, nine3_conj_fibre h hdF.1 hdF.2 heF.1 heF.2,
        T.mul_mem (T.mul_mem heT hdT) (T.inv_mem heT)⟩
    have hrefl_s : ∀ a ∈ L, 2 * s - a ∈ L := fun a ha => hconj ha hsL
    have hrefl_r : ∀ a ∈ L, 2 * r - a ∈ L := fun a ha => hconj ha hrL
    let u : ZMod p := 2 * (s - r)
    have hstep : ∀ a ∈ L, a + u ∈ L := by
      intro a ha
      have h1 := hrefl_r a ha
      have h2 := hrefl_s (2 * r - a) h1
      have heq : 2 * s - (2 * r - a) = a + u := by simp only [u]; ring
      rwa [heq] at h2
    have hstep' : ∀ a ∈ L, a - u ∈ L := by
      intro a ha
      have h1 := hrefl_s a ha
      have h2 := hrefl_r (2 * s - a) h1
      have heq : 2 * r - (2 * s - a) = a - u := by simp only [u]; ring
      rwa [heq] at h2
    have hmem : ∀ n : ℤ, r + n • u ∈ L := by
      intro n
      refine Int.induction_on n ?_ ?_ ?_
      · simpa using hrL
      · intro k hkL
        have h := hstep (r + (k : ℤ) • u) hkL
        have heq : r + (k : ℤ) • u + u = r + ((k + 1 : ℕ) : ℤ) • u := by
          simp only [zsmul_eq_mul]
          push_cast
          ring
        rwa [heq] at h
      · intro k hkL
        have h := hstep' (r + (-(k : ℤ)) • u) hkL
        have heq : r + (-(k : ℤ)) • u - u = r + ((-(k : ℤ)) - 1) • u := by
          simp only [zsmul_eq_mul]
          push_cast
          ring
        rwa [heq] at h
    have hu : u ≠ 0 := by
      simp only [u]
      exact mul_ne_zero (nine3_two_ne_zero hp hp2) (sub_ne_zero.mpr (Ne.symm hrs))
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hsurj : ∃ n : ℤ, r + n • u = c := by
      refine ⟨(((c - r) * u⁻¹).val : ℤ), ?_⟩
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [mul_assoc, inv_mul_cancel₀ hu, mul_one]
      ring
    obtain ⟨n, hn⟩ := hsurj
    rw [← hn]
    exact hmem n
  have hDT : D ⊆ T := by
    intro d hd
    obtain ⟨c, hc⟩ := h.refl d hd
    have hdF : d ∈ F c := ⟨hd, hc⟩
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmp
      · exfalso
        have h0 : Nat.card ↥(F c) = 0 := by rw [hcardF c, hm0]
        exact (Nat.card_ne_zero.mpr ⟨⟨d, hdF⟩, inferInstance⟩) h0
      · exact hmp
    obtain ⟨e, heF, heT⟩ := hreach hm c
    by_cases hcs : c = s
    · rw [hcs] at hdF
      exact hFsT hdF
    · obtain ⟨z, hz, hze⟩ := h.trans c s hcs e heF.1 heF.2 d hdF.1 hdF.2
      have hzT : z ∈ T := hFs_le hz.1
      rw [← hze]
      exact T.mul_mem (T.mul_mem hzT heT) (T.inv_mem hzT)
  change T = ⊤
  rw [eq_top_iff, ← h.gen]
  exact (Subgroup.closure_le T).mpr hDT

theorem nine3OddFrame_card_inf_ker (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) (c : ZMod p) :
    Nat.card ↥(Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) = 8 := by
  classical
  let F : Set Γ := nine3FibreSet π D c
  let E : Subgroup Γ := Subgroup.closure F
  have hcomm : F.Pairwise Commute := by
    intro d hd e he _
    exact h.comm d hd.1 e he.1 (hd.2.trans he.2.symm)
  letI : CommGroup E := Subgroup.closureCommGroupOfComm hcomm
  haveI : Finite ↥F := Finite.of_injective (Subtype.val : ↥F → Γ) Subtype.val_injective
  haveI : Fintype ↥F := Fintype.ofFinite ↥F
  let φ : ↥F → E := fun d => ⟨(d : Γ), Subgroup.subset_closure d.2⟩
  have hφ_sq : ∀ d : ↥F, φ d * φ d = 1 := by
    intro d
    apply Subtype.ext
    simpa [φ] using h.sq d.1 d.2.1
  have hφ_sq' : ∀ d : ↥F, φ d ^ 2 = 1 := fun d => by rw [pow_two]; exact hφ_sq d
  have hclosure : Subgroup.closure (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    have hx : (x : Γ) ∈
        (Subgroup.closure (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F))).map E.subtype := by
      rw [MonoidHom.map_closure]
      have himg : E.subtype '' (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F)) = F := by
        ext y; constructor
        · rintro ⟨z, ⟨i, -, rfl⟩, rfl⟩
          exact i.2
        · intro hy
          exact ⟨φ ⟨y, hy⟩, ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩, rfl⟩
      rw [himg]
      exact x.2
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hinj : Set.InjOn (fun S : Finset ↥F => ∏ d ∈ S, φ d)
      ((Finset.univ : Finset ↥F).powerset : Set (Finset ↥F)) := by
    intro S _ T _ hST
    have hST' : (∏ d ∈ S, φ d) = ∏ d ∈ T, φ d := hST
    by_contra hne
    have hrel : ∏ d ∈ S ∆ T, φ d = 1 := by
      have hsd := TauCeti.prod_sdiff_union_sdiff φ (S := S) (D := T)
        (fun i _ => hφ_sq' i)
      rw [Finset.symmDiff_def, hsd, hST']
      rw [← sq, ← Finset.prod_pow]
      exact Finset.prod_eq_one (fun i _ => hφ_sq' i)
    have hne' : (S ∆ T).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      exact hne (Finset.symmDiff_eq_empty.mp hemp)
    set l : List Γ := (S ∆ T).toList.map (fun d : ↥F => (d : Γ)) with hl
    have hl_nodup : l.Nodup := by
      rw [hl]
      exact List.Nodup.map (fun _ _ hab => Subtype.ext hab) (S ∆ T).nodup_toList
    have hl_ne : l ≠ [] := by
      rw [hl]
      intro hnil
      exact Finset.nonempty_iff_ne_empty.mp hne'
        (Finset.toList_eq_nil.mp (List.map_eq_nil_iff.mp hnil))
    have hl_mem : ∀ d ∈ l, d ∈ D ∧ π d = zmodRefl p c := by
      intro d hd
      rw [hl] at hd
      obtain ⟨d', _, rfl⟩ := List.mem_map.mp hd
      exact d'.2
    have hl_prod : l.prod = 1 := by
      rw [hl]
      have h1 := List.prod_map_hom (S ∆ T).toList φ E.subtype
      rw [show (fun d : ↥F => (d : Γ)) = (E.subtype ∘ φ) from rfl, h1,
        Finset.prod_map_toList, hrel, map_one]
    exact hi c l hl_nodup hl_ne hl_mem hl_prod
  have hcardE : Nat.card E = 16 := by
    have htau := TauCeti.natCard_closure_image_eq_two_pow (s := Finset.univ) (f := φ)
      (fun i _ => hφ_sq' i) hinj
    rw [hclosure, Subgroup.card_top] at htau
    rw [htau, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [show Nat.card ↥F = 4 from h.card c]
    norm_num
  let f : E →* Equiv.Perm (ZMod p) := π.comp E.subtype
  have hker : Nat.card ↥f.ker = Nat.card ↥(E ⊓ π.ker) := by
    have heq : f.ker = (E ⊓ π.ker).subgroupOf E := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, f,
        MonoidHom.comp_apply, Subgroup.subtype_apply]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card ↥f.range = 2 := by
    have hFne : F.Nonempty := by
      have hpos : 0 < Nat.card ↥F := by
        rw [show Nat.card ↥F = 4 from h.card c]
        norm_num
      exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
    have hrange_eq : f.range = Subgroup.zpowers (zmodRefl p c) := by
      have hfr : f.range = E.map π := by
        rw [show f = π.comp E.subtype from rfl, MonoidHom.range_comp,
          Subgroup.range_subtype]
      rw [hfr]
      change (Subgroup.closure F).map π = Subgroup.zpowers (zmodRefl p c)
      rw [MonoidHom.map_closure]
      have himage : π '' F = {zmodRefl p c} := by
        ext x; constructor
        · rintro ⟨d, hd, rfl⟩
          exact hd.2
        · intro hx
          obtain ⟨d, hd⟩ := hFne
          exact ⟨d, hd, by rw [hd.2, hx]⟩
      rw [himage, ← Subgroup.zpowers_eq_closure]
    rw [hrange_eq, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact nine3_zmodRefl_sq c)
      (nine3_zmodRefl_ne_one hp hp2 c)
  have hmain := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, hcardE] at hmain
  change Nat.card ↥(E ⊓ π.ker) = 8
  omega

theorem nine3OddFrame_inf_le_center (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    {r s : ZMod p} (hrs : r ≠ s) :
    Subgroup.closure (nine3FibreSet π D r) ⊓ Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker ≤
      Subgroup.center Γ := by
  intro w hw
  rw [Subgroup.mem_center_iff]
  intro y
  have hcommr : ∀ d ∈ nine3FibreSet π D r, Commute d w :=
    fun d hd => nine3_closure_commute h hw.1.1 hd
  have hcomms : ∀ d ∈ nine3FibreSet π D s, Commute d w :=
    fun d hd => nine3_closure_commute h hw.1.2 hd
  have hy : y ∈ Subgroup.closure (nine3FibreSet π D r ∪ nine3FibreSet π D s) := by
    rw [nine3OddFrame_closure_two hp hp2 h hrs]
    exact Subgroup.mem_top y
  have hcomm : Commute y w := by
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · exact hcommr x hx
        · exact hcomms x hx
    | one => exact Commute.one_left w
    | mul a b _ _ iha ihb => exact iha.mul_left ihb
    | inv a _ iha => exact iha.inv_left
  exact hcomm.eq

theorem nine3OddFrame_card_inf_le_two (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) {r s : ZMod p} (hrs : r ≠ s) :
    Nat.card ↥(Subgroup.closure (nine3FibreSet π D r) ⊓ Subgroup.closure (nine3FibreSet π D s) ⊓
      π.ker) ≤ 2 := by
  classical
  have hFr_ne : (nine3FibreSet π D r).Nonempty := by
    have hpos : 0 < Nat.card ↥(nine3FibreSet π D r) := by
      rw [show Nat.card ↥(nine3FibreSet π D r) = 4 from h.card r]
      norm_num
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
  obtain ⟨d, hd⟩ := hFr_ne
  let d' : ↥(nine3FibreSet π D r) := ⟨d, hd⟩
  let Z : Subgroup Γ := Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker
  let act : Z → ↥(nine3FibreSet π D r) → ↥(nine3FibreSet π D r) :=
    fun z e => ⟨z.1 * e.1 * z.1⁻¹, h.conj e.1 e.2.1 z.1, by
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp z.2.2, e.2.2]
      simp⟩
  letI : MulAction Z ↥(nine3FibreSet π D r) :=
    { smul := act
      one_smul := by
        intro e
        apply Subtype.ext
        show ((1 : Z) : Γ) * (e : Γ) * ((1 : Z) : Γ)⁻¹ = (e : Γ)
        simp
      mul_smul := by
        intro z z' e
        apply Subtype.ext
        show ((z * z' : Z) : Γ) * (e : Γ) * ((z * z' : Z) : Γ)⁻¹ =
          (z : Γ) * ((z' : Γ) * (e : Γ) * (z' : Γ)⁻¹) * (z : Γ)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc] }
  haveI : Fintype Z := Fintype.ofFinite Z
  haveI : Fintype (MulAction.orbit Z d') := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer Z d') := Fintype.ofFinite _
  have horbit : MulAction.orbit Z d' = Set.univ := by
    ext e; constructor
    · intro _
      exact Set.mem_univ e
    · intro _
      rw [MulAction.mem_orbit_iff]
      obtain ⟨z, hz, hze⟩ := h.trans r s hrs d hd.1 hd.2 e.1 e.2.1 e.2.2
      exact ⟨⟨z, hz⟩, by apply Subtype.ext; exact hze⟩
  have horbit_card : Fintype.card (MulAction.orbit Z d') = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, horbit, Set.ncard_univ]
    exact h.card r
  have hZcard : Fintype.card Z = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact nine3OddFrame_card_inf_ker hp hp2 h hi s
  have hstab_card : Nat.card ↥(MulAction.stabilizer Z d') = 2 := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := Z) d'
    rw [horbit_card, hZcard] at hos
    have h2 : Fintype.card (MulAction.stabilizer Z d') = 2 := by omega
    rwa [Nat.card_eq_fintype_card]
  have hle : Subgroup.closure (nine3FibreSet π D r) ⊓ Subgroup.closure (nine3FibreSet π D s) ⊓
      π.ker ≤ Z := le_inf (le_trans inf_le_left inf_le_right) inf_le_right
  have hstab : (Subgroup.closure (nine3FibreSet π D r) ⊓ Subgroup.closure (nine3FibreSet π D s) ⊓
      π.ker).subgroupOf Z ≤ MulAction.stabilizer Z d' := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    have hwr : (w : Γ) ∈ Subgroup.closure (nine3FibreSet π D r) := hw.1.1
    have hcomm : Commute d (w : Γ) := nine3_closure_commute h hwr hd
    show (w : Γ) * d * (w : Γ)⁻¹ = d
    rw [hcomm.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hcard_le : Nat.card ↥(Subgroup.closure (nine3FibreSet π D r) ⊓
      Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) ≤
      Nat.card ↥(MulAction.stabilizer Z d') := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_le_of_le hstab
  omega

end CFSG.LocalAnalysis.WeakClosure81
