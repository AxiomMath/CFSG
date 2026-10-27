module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace F6

@[expose] def NativeTheoremCSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
    ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)],
      (∃ a b : H ⧸ N, a * b ≠ b * a) → CFSG.Milestones.SQTKSimpleList (H ⧸ N)

theorem sqtkSimpleList_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Milestones.SQTKSimpleList Y) : CFSG.Milestones.SQTKSimpleList X := by
  open CFSG.SectionRank in
  rcases h with ⟨n, h5, h8, ⟨e'⟩⟩ | ⟨p, hp, hp2, h⟩ | h | ⟨n, hn, h⟩ | ⟨s, hs, ⟨e'⟩⟩
  · exact Or.inl ⟨n, h5, h8, ⟨e.trans e'⟩⟩
  · refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    rcases h with ⟨f, hf, h⟩ | h | h
    · exact Or.inl ⟨f, hf, statedClassicalModel_of_mulEquiv e h⟩
    · exact Or.inr (Or.inl (statedClassicalModel_of_mulEquiv e h))
    · exact Or.inr (Or.inr (statedClassicalModel_of_mulEquiv e h))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rcases h with ⟨f, h⟩ | h
    · refine Or.inl ⟨f, ?_⟩
      rcases h with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, hf', h⟩ |
          ⟨hf, hf', h⟩
      · exact Or.inl ⟨hf, statedClassicalModel_of_mulEquiv e h⟩
      · exact Or.inr (Or.inl ⟨hf, statedClassicalModel_of_mulEquiv e h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hf, statedClassicalModel_of_mulEquiv e h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, statedClassicalModel_of_mulEquiv e h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hf, chevalleyExceptionalModel_of_mulEquiv e h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hf, chevalleyExceptionalModel_of_mulEquiv e h⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hf, hf', reeTitsModel_of_mulEquiv e h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hf, hf', suzukiModel_of_mulEquiv e h⟩))))))
    · exact Or.inr (reeTitsModel_of_mulEquiv e h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, statedClassicalModel_of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, ⟨e.trans e'⟩⟩)))

theorem isPGroup_center_of_pPrimeCore_eq_bot {D : Type} [Group D] [Finite D]
    (hO : CFSG.pPrimeCore 3 D = ⊥) {L : Subgroup D} [hLn : L.Normal] :
    IsPGroup 3 ↥(Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, r, hr, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := D)).ne' 3 (by norm_num)
  set A : Subgroup D := L ⊓ Subgroup.centralizer (L : Set D) with hA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).1).symm
  set S : Set D := {s | ∃ z ∈ A, z ^ 3 ^ a = s} with hS
  set W : Subgroup D := Subgroup.closure S with hW
  have hWA : W ≤ A := (Subgroup.closure_le _).mpr fun s ⟨z, hz, hs⟩ => hs ▸ A.pow_mem hz _
  have hWr : ∀ w ∈ W, w ^ r = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨z, -, rfl⟩ := hs
      rw [← pow_mul, ← hn, pow_card_eq_one']
    | one => exact one_pow r
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hAc x (hWA hx) y (hWA hy)) r), ihx, ihy, one_mul]
    | inv x _ ihx => rw [inv_pow, ihx, inv_one]
  have hAn : ∀ g : D, ∀ z ∈ A, g * z * g⁻¹ ∈ A := by
    intro g z hz
    refine Subgroup.mem_inf.mpr ⟨hLn.conj_mem z (Subgroup.mem_inf.mp hz).1 g, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by simpa using hLn.conj_mem l hl g⁻¹
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ hl'
    calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * l := by group
  have hWn : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    induction hw using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨z, hz, rfl⟩ := hs
      exact Subgroup.subset_closure ⟨g * z * g⁻¹, hAn g z hz, by rw [conj_pow]⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact W.mul_mem ihx ihy
    | inv x _ ihx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact W.inv_mem ihx
  have hcop : Nat.Coprime 3 (Nat.card W) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hr ?_
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h1 : (w : D) ^ r = 1 := hWr w w.2
    have h2 : w ^ r = 1 := Subtype.ext (by simpa using h1)
    rw [← hw]
    exact orderOf_dvd_of_pow_eq_one h2
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hWn, hcop⟩
  intro g
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  have hgA : ((g : L) : D) ∈ A := by
    refine Subgroup.mem_inf.mpr ⟨(g : L).2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp g.2 ⟨l, hl⟩)
  have hmem : ((g : L) : D) ^ 3 ^ a ∈ W := Subgroup.subset_closure ⟨_, hgA, rfl⟩
  rw [hWbot, Subgroup.mem_bot] at hmem
  simpa using hmem

theorem sqtkSimpleList_of_isQuasisimple (hC : NativeTheoremCSection) {D X : Type} [Group D]
    [Group X] [Finite X] (hX : CFSG.SectionRank.IsSQTKCat X) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X)
    {L : Subgroup D} (hq : CFSG.IsQuasisimple ↥L) :
    CFSG.Milestones.SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  set H : Subgroup X := (L.map e.toMonoidHom).comap π with hH
  have hmemL : ∀ h : ↥H, e.symm (π h) ∈ L := by
    intro h
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp h.2)
    have : e.symm (π h) = l := by
      rw [← hle]
      exact e.symm_apply_apply l
    rw [this]
    exact hl
  let ψ : ↥H →* ↥L :=
    (e.symm.toMonoidHom.comp (π.comp H.subtype)).codRestrict L hmemL
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 X) (e l)
    have hxH : x ∈ H := by
      rw [hH, Subgroup.mem_comap, hx]
      exact Subgroup.mem_map_of_mem _ l.2
    refine ⟨⟨x, hxH⟩, Subtype.ext ?_⟩
    change e.symm (π x) = l
    rw [hx, MulEquiv.symm_apply_apply]
  let φ : ↥H →* ↥L ⧸ Subgroup.center ↥L := (QuotientGroup.mk' (Subgroup.center ↥L)).comp ψ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  let iso : ↥H ⧸ φ.ker ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have : IsSimpleGroup (↥H ⧸ φ.ker) := iso.isSimpleGroup
  have hnonab : ∃ a b : ↥H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
    have := congrArg iso h
    simpa using this
  exact sqtkSimpleList_of_mulEquiv iso.symm (hC X hX H φ.ker hnonab)

structure F618RecogSetting (D : Type) [Group D] [Finite D] : Prop where
  fitting : CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D)
  quasisimple : CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))
  list : CFSG.Milestones.SQTKSimpleList
    (↥(twoResidual (⊤ : Subgroup D)) ⧸ Subgroup.center ↥(twoResidual (⊤ : Subgroup D)))
  center : IsPGroup 3 ↥(Subgroup.center ↥(twoResidual (⊤ : Subgroup D)))
  o2 : Open.pCore 2 D = ⊥

theorem twoResidual_top_normal {D : Type} [Group D] :
    (twoResidual (⊤ : Subgroup D)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))

theorem f618RecogSetting_of (hC : NativeTheoremCSection) {D : Type} [Group D] [Finite D]
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X))
    (hF : CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D))
    (hL : CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) : F618RecogSetting D := by
  obtain ⟨X, _, _, hsq, ⟨e⟩⟩ := hX
  obtain ⟨hO, hO2⟩ := remark_f6_15 e
  have := twoResidual_top_normal (D := D)
  exact ⟨hF, hL, sqtkSimpleList_of_isQuasisimple hC hsq e hL,
    isPGroup_center_of_pPrimeCore_eq_bot hO, hO2⟩

theorem false_of_isGoldCaseI {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (hL : CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D)))
    (hI : IsGoldCaseI G₁ G₂) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := h.sylow
  obtain ⟨-, ⟨eT⟩, -⟩ := hI
  have hTc : IsCyclic (T : Subgroup D) := by
    rw [hT]
    exact isCyclic_of_surjective eT.symm.toMonoidHom eT.symm.surjective
  have hT2 : Nat.card (T : Subgroup D) = 2 := by
    rw [hT, Nat.card_congr eT.toEquiv]
    simp
  obtain ⟨N, hN, hNT⟩ := exists_normal_isComplement'_of_isCyclic_sylow
    (fun q hq _ => hq.two_le) T hTc
  have hcard : Nat.card N * 2 = Nat.card D := by
    rw [← hT2]
    exact hNT.card_mul_card
  have hodd : Odd (Nat.card N) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h4 : 2 ^ 2 ∣ Nat.card D := by
      rw [← hcard, pow_two]
      exact Nat.mul_dvd_mul_right (Nat.dvd_of_mod_eq_zero (by omega)) 2
    have hle := (Sylow.pow_dvd_card_of_pow_dvd_card (P := T) h4)
    rw [hT2] at hle
    exact absurd (Nat.le_of_dvd (by norm_num) hle) (by norm_num)
  have hLN : twoResidual (⊤ : Subgroup D) ≤ N := by
    refine twoResidual_le_of_isTwoQuotient le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hN]) fun y _ => ?_
    obtain ⟨⟨n, t⟩, hy⟩ := hNT.2 y
    obtain ⟨k, hk⟩ := (T.isPGroup') t
    refine ⟨k, ?_⟩
    have hmod : (QuotientGroup.mk (y ^ 2 ^ k) : D ⧸ N) = 1 := by
      rw [← hy, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (n : D)).mpr n.2, one_mul, ← QuotientGroup.mk_pow]
      rw [QuotientGroup.eq_one_iff]
      have : ((t : D)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact N.one_mem
    exact (QuotientGroup.eq_one_iff _).mp hmod
  have hLodd : Odd (Nat.card ↥(twoResidual (⊤ : Subgroup D))) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hLN)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hLodd
  have : Nontrivial ↥(twoResidual (⊤ : Subgroup D)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hL
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hL.1
  exact Group.IsPerfect.not_isSolvable (G := ↥(twoResidual (⊤ : Subgroup D))) hsolv

end F6

end CFSG.Quasithin
