module

public import CFSG.Quasithin.Background.A3Structure318Quot
import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.Quasithin.Background.A3Structure36AList
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Quasithin

namespace A318

open CFSG.Open CFSG.SectionRank CFSG.Quasithin.A320
open scoped commutatorElement

theorem pCore_two_le_pPrimeCore {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) : CFSG.pCore 2 H ≤ CFSG.pPrimeCore p H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (Nat.card (CFSG.pCore 2 H)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := H) (p := 2))
    rw [hn]
    exact ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2).pow_right n
  exact le_sSup ⟨inferInstance, hcop⟩

theorem map_pCore_le_pCore {H : Type*} [Group H] {p : ℕ} (L : Subgroup H) [L.Normal] :
    (CFSG.pCore p ↥L).map L.subtype ≤ CFSG.pCore p H := by
  have hn : ((CFSG.pCore p ↥L).map L.subtype).Normal := ⟨fun n hn g => by
    obtain ⟨x, hx, rfl⟩ := hn
    refine ⟨MulAut.conjNormal g x, ?_, ?_⟩
    · have := CFSG.pCore_map_iso p (MulAut.conjNormal g : ↥L ≃* ↥L)
      rw [← this]
      exact ⟨x, hx, rfl⟩
    · rfl⟩
  exact le_sSup ⟨hn, IsPGroup.map CFSG.pCore_isPGroup L.subtype⟩

theorem isSolvable_ker_comp {A B C : Type*} [Group A] [Group B] [Group C] (φ : A →* B)
    (ρ : B →* C) (hφ : Group.IsSolvable φ.ker) (hρ : ρ.ker ≤ Subgroup.center B) :
    Group.IsSolvable (ρ.comp φ).ker := by
  have hle : φ.ker ≤ (ρ.comp φ).ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [hx]
  let f : ↥φ.ker →* ↥(ρ.comp φ).ker := Subgroup.inclusion hle
  let g : ↥(ρ.comp φ).ker →* ↥(Subgroup.center B) :=
    (φ.comp (ρ.comp φ).ker.subtype).codRestrict (Subgroup.center B) fun x =>
      hρ (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2))
  have : Group.IsSolvable ↥(Subgroup.center B) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro x hx
  have hx1 : φ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact ⟨⟨(x : A), hx1⟩, rfl⟩

theorem generalizedFitting_eq_top_of_quasisimple {X : Type*} [Group X]
    (hQ : CFSG.IsQuasisimple X) : CFSG.generalizedFitting X = ⊤ :=
  CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hQ

theorem specialLinear_two_nontrivial (p : ℕ) [Fact p.Prime] :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), m ≠ 1 := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (m : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp at this

theorem not_case34_of_quasisimple {X : Type} [Group X] (hQ : CFSG.IsQuasisimple X) :
    ¬ (A36Case3 X ∨ A36Case4 X) := by
  have hF := generalizedFitting_eq_top_of_quasisimple hQ
  rintro (⟨p, hp, hp3, hgf, -, e, ψ, hψs, hψk, -⟩ | ⟨hgf, -, ⟨e⟩, -⟩)
  · have : Fact p.Prime := ⟨hp⟩
    have hFtop : CFSG.fittingSubgroup X = ⊤ := hgf ▸ hF
    obtain ⟨m, hm⟩ := specialLinear_two_nontrivial p
    obtain ⟨x, rfl⟩ := hψs m
    apply hm
    have : x ∈ ψ.ker := by
      rw [hψk, hFtop]
      exact Subgroup.mem_top x
    exact this
  · have hFtop : CFSG.fittingSubgroup X = ⊤ := hgf ▸ hF
    have : Subsingleton (X ⧸ CFSG.fittingSubgroup X) := QuotientGroup.subsingleton_iff.mpr hFtop
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨m, hm⟩ := specialLinear_two_nontrivial 5
    exact hm (e.symm.injective (Subsingleton.elim _ _))

theorem a36Case2List_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : A36Case2List X) : A36Case2List Y := by
  rcases h with ⟨s, p, n, hp, hn, hcong, hX⟩ | h | h | h
  · exact Or.inl ⟨s, p, n, hp, hn, hcong, IsSLEps3.of_mulEquiv e hX⟩
  · exact Or.inr (Or.inl (IsHat.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (IsHat.of_mulEquiv e h)))

theorem lBar_structure {H : Type} [Group H] [Finite H] (h36 : A36Statement (H ⧸ CFSG.pCore 2 H))
    {L : Subgroup H} (hL : L ∈ cComp (⊤ : Subgroup H)) [L.Normal]
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.IsQuasisimple ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 H))) ∧
      ((Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 H))) = ⊥ ∧
          A23List ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) ∨
        (Nat.card (Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) = 3 ∧
          A36Case2List ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 H))))) := by
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  have hLbar := mem_cComp_quotient hL
  have hker : CFSG.pCore 2 ↥L ≤ (π.subgroupMap L).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have h1 : (x : H) ∈ CFSG.pCore 2 H := map_pCore_le_pCore L ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 h1
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(L.map π) := QuotientGroup.lift _ (π.subgroupMap L) hker
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := π.subgroupMap_surjective L y
    exact ⟨QuotientGroup.mk x, hx⟩
  have hne : ∃ k, ψ k ≠ 1 := by
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (ne_bot_of_mem_cComp hLbar)
    obtain ⟨k, hk⟩ := hψ y
    exact ⟨k, by rw [hk]; exact hy1⟩
  have hQ' : CFSG.IsQuasisimple ↥(L.map π) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hQ hψ hne
  refine ⟨hQ', ?_⟩
  obtain ⟨hconc, -, -⟩ := h36 _ hLbar
  rcases hconc with ⟨-, hsimple, hlist⟩ | ⟨-, hcard, hlist⟩ | h3 | h4
  · left
    refine ⟨?_, hlist⟩
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(L.map π)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hQ'.2.2
      have : Subsingleton (↥(L.map π) ⧸ Subgroup.center ↥(L.map π)) :=
        QuotientGroup.subsingleton_iff.mpr h
      exact hab (Subsingleton.elim _ _)
  · exact Or.inr ⟨hcard, hlist⟩
  · exact absurd (Or.inl h3) (not_case34_of_quasisimple hQ')
  · exact absurd (Or.inr h4) (not_case34_of_quasisimple hQ')

theorem star_structure (hlist : A23SQTKListFact) {H : Type} [Group H] [Finite H]
    (hH : SQTKGroup H) (h36 : A36Statement (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) [L.Normal]
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank p L) :
    CFSG.IsQuasisimple ↥(starImage p L) ∧ 2 ≤ CFSG.Open.pRank p (starImage p L) ∧
      (Subgroup.center ↥(starImage p L) = ⊥ → A23List ↥(starImage p L)) ∧
      (Subgroup.center ↥(starImage p L) ≠ ⊥ → p = 3 ∧
        Nat.card (Subgroup.center ↥(starImage p L)) = 3 ∧ A36Case2List ↥(starImage p L)) ∧
      Group.IsSolvable ↥((CFSG.pPrimeCore p H).subgroupOf L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  let π' : H →* PStar p H := QuotientGroup.mk' (CFSG.pPrimeCore p H)
  have hN₂N : CFSG.pCore 2 H ≤ CFSG.pPrimeCore p H := pCore_two_le_pPrimeCore hp2
  let ρ : H ⧸ CFSG.pCore 2 H →* PStar p H :=
    QuotientGroup.map (CFSG.pCore 2 H) (CFSG.pPrimeCore p H) (MonoidHom.id H)
      (fun x hx => hN₂N hx)
  have hρ : ∀ x : H, ρ (π x) = π' x := fun x => rfl
  obtain ⟨hQt, hcases⟩ := lBar_structure h36 hL hQ
  have hSmem : ∀ x : ↥(L.map π), ρ x ∈ starImage p L := by
    rintro ⟨_, l, hl, rfl⟩
    exact ⟨l, hl, (hρ l).symm ▸ rfl⟩
  let ρ₁ : ↥(L.map π) →* ↥(starImage p L) := (ρ.comp (L.map π).subtype).codRestrict _ hSmem
  have hρ₁ : Function.Surjective ρ₁ := by
    rintro ⟨_, l, hl, rfl⟩
    exact ⟨⟨π l, l, hl, rfl⟩, Subtype.ext rfl⟩
  have hker' : Nat.Coprime p (Nat.card π'.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have h2S : 2 ≤ CFSG.Open.pRank p (starImage p L) :=
    hrank.trans (pRank_le_pRank_map_of_coprime π' hker' L)
  have hSne : ∃ k : ↥(L.map π), ρ₁ k ≠ 1 := by
    obtain ⟨X, hXS, -, hXcard⟩ := exists_subgroup_card_prime (p := p)
      (H := starImage p L) (by omega)
    have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 (by
      rw [hXcard]
      exact hp.out.one_lt)
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨k, hk⟩ := hρ₁ ⟨x, hXS x.2⟩
    refine ⟨k, fun h => hx (Subtype.ext ?_)⟩
    have := congrArg Subtype.val (hk.symm.trans h)
    simpa using this
  have hS : CFSG.IsQuasisimple ↥(starImage p L) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hQt hρ₁ hSne
  have hkerρ : ρ₁.ker ≤ Subgroup.center ↥(L.map π) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hQt hSne
  have hcenter : Subgroup.center ↥(starImage p L) = (Subgroup.center ↥(L.map π)).map ρ₁ :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hQt hρ₁ hkerρ
  have hsolv : Group.IsSolvable ↥((CFSG.pPrimeCore p H).subgroupOf L) := by
    have hφ₂ : Group.IsSolvable (π.subgroupMap L).ker := by
      let ι : ↥(π.subgroupMap L).ker →* ↥(CFSG.pCore 2 H) :=
        ((L.subtype).comp (π.subgroupMap L).ker.subtype).codRestrict _ fun x =>
          (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val (MonoidHom.mem_ker.1 x.2))
      have hι : Function.Injective ι := fun a b hab => by
        have h1 : ((a : ↥L) : H) = ((b : ↥L) : H) :=
          congrArg (fun z : ↥(CFSG.pCore 2 H) => (z : H)) hab
        exact Subtype.ext (Subtype.ext h1)
      have hP : IsPGroup 2 ↥(π.subgroupMap L).ker :=
        IsPGroup.of_injective CFSG.pCore_isPGroup ι hι
      have : Group.IsNilpotent ↥(π.subgroupMap L).ker := hP.isNilpotent
      infer_instance
    have h1 := isSolvable_ker_comp (π.subgroupMap L) ρ₁ hφ₂ hkerρ
    have heq : (ρ₁.comp (π.subgroupMap L)).ker = (CFSG.pPrimeCore p H).subgroupOf L := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx))
      · intro hx
        exact MonoidHom.mem_ker.2 (Subtype.ext
          ((QuotientGroup.eq_one_iff (x : H)).2 (Subgroup.mem_subgroupOf.1 hx)))
    rw [← heq]
    exact h1
  have hSn : (starImage p L).Normal :=
    Subgroup.Normal.map ‹L.Normal› π' (QuotientGroup.mk'_surjective _)
  have hO : CFSG.pPrimeCore p (PStar p H) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hGH : SQTKGroup (H ⧸ CFSG.pCore 2 H) := (SQTKHyp.of_sqtkGroup H hH).sqtkGroup
  have hdich : (Subgroup.center ↥(starImage p L) = ⊥ ∧ A23List ↥(starImage p L)) ∨
      (p = 3 ∧ Nat.card (Subgroup.center ↥(starImage p L)) = 3 ∧
        A36Case2List ↥(starImage p L)) := by
    rcases hcases with ⟨hZ, hlistL⟩ | ⟨hcard, hlistL⟩
    ·
      have hinj : Function.Injective ρ₁ := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have := hkerρ (MonoidHom.mem_ker.2 hx)
        rw [hZ, Subgroup.mem_bot] at this
        exact this
      let e : ↥(L.map π) ≃* ↥(starImage p L) := MulEquiv.ofBijective ρ₁ ⟨hinj, hρ₁⟩
      left
      refine ⟨?_, A36A.a23List_of_mulEquiv e.symm hlistL⟩
      rw [hcenter, hZ, Subgroup.map_bot]
    · have : Fact (Nat.Prime (Nat.card (Subgroup.center ↥(L.map π)))) :=
        ⟨by rw [hcard]; exact Nat.prime_three⟩
      by_cases hker1 : ρ₁.ker = ⊥
      ·
        have hinj : Function.Injective ρ₁ := (MonoidHom.ker_eq_bot_iff _).1 hker1
        let e : ↥(L.map π) ≃* ↥(starImage p L) := MulEquiv.ofBijective ρ₁ ⟨hinj, hρ₁⟩
        have hcardS : Nat.card (Subgroup.center ↥(starImage p L)) = 3 := by
          rw [hcenter, Subgroup.card_map_of_injective hinj, hcard]
        have hp3 : p = 3 := by
          by_contra hne
          have hZ'n : ((Subgroup.center ↥(starImage p L)).map (starImage p L).subtype).Normal :=
            ⟨fun n hn g => by
              obtain ⟨z, hz, rfl⟩ := hn
              refine ⟨MulAut.conjNormal g z, ?_, rfl⟩
              change z ∈ Subgroup.center ↥(starImage p L) at hz
              change (MulAut.conjNormal g) z ∈ Subgroup.center ↥(starImage p L)
              rw [Subgroup.mem_center_iff] at hz ⊢
              intro y
              have h1 := congrArg (MulAut.conjNormal g) (hz ((MulAut.conjNormal g).symm y))
              simpa using h1⟩
          have hcop : Nat.Coprime p
              (Nat.card ↥((Subgroup.center ↥(starImage p L)).map (starImage p L).subtype)) := by
            rw [Subgroup.card_map_of_injective (starImage p L).subtype_injective, hcardS]
            exact (Nat.coprime_primes hp.out Nat.prime_three).2 hne
          have hle : (Subgroup.center ↥(starImage p L)).map (starImage p L).subtype ≤
              CFSG.pPrimeCore p (PStar p H) := le_sSup ⟨hZ'n, hcop⟩
          rw [hO] at hle
          have hbot : Subgroup.center ↥(starImage p L) = ⊥ := by
            rw [eq_bot_iff]
            intro z hz
            exact Subtype.ext (Subgroup.mem_bot.1 (hle ⟨z, hz, rfl⟩))
          rw [hbot] at hcardS
          simp at hcardS
        exact Or.inr ⟨hp3, hcardS, a36Case2List_of_mulEquiv e hlistL⟩
      ·
        have hkerZ : ρ₁.ker = Subgroup.center ↥(L.map π) := by
          rcases Subgroup.eq_bot_or_eq_top_of_prime_card
              (ρ₁.ker.subgroupOf (Subgroup.center ↥(L.map π))) with h | h
          · exact absurd ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hkerρ) hker1
          · exact le_antisymm hkerρ (Subgroup.subgroupOf_eq_top.1 h)
        have hZS : Subgroup.center ↥(starImage p L) = ⊥ := by
          rw [hcenter, ← hkerZ]
          exact (Subgroup.map_eq_bot_iff _).2 le_rfl
        let e' : ↥(L.map π) ⧸ Subgroup.center ↥(L.map π) ≃* ↥(starImage p L) :=
          (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁)
        have hlistQ : A23List (↥(L.map π) ⧸ Subgroup.center ↥(L.map π)) :=
          hlist _ hGH (L.map π) (Subgroup.center ↥(L.map π)) hQt.2.1 hQt.2.2
        exact Or.inl ⟨hZS, A36A.a23List_of_mulEquiv e'.symm hlistQ⟩
  refine ⟨hS, h2S, fun hZ => ?_, fun hZ => ?_, hsolv⟩
  · rcases hdich with ⟨-, h⟩ | ⟨-, hc, -⟩
    · exact h
    · exfalso
      rw [hZ] at hc
      simp at hc
  · rcases hdich with ⟨h, -⟩ | h
    · exact absurd h hZ
    · exact h

end A318

end CFSG.Quasithin
