module

public import CFSG.Quasithin.Background.C35InspLift
public import CFSG.Quasithin.Background.C48PfFourModPfGrp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod

variable {A : Type} [Group A] [Finite A]

theorem img_perfectCore {K : Subgroup A} {G' : Type} [Group G'] [Finite G'] (φ : ↥K →* G')
    {X : Subgroup A} (hXK : X ≤ K) : img φ (perfectCore X) = perfectCore (img φ X) := by
  have h1 : (perfectCore X).subgroupOf K = perfectCore (X.subgroupOf K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le X).trans hXK), map_perfectCore,
      Subgroup.map_subgroupOf_eq_of_le hXK]
  rw [img, h1, map_perfectCore, img]

omit [Finite A] in
theorem centerOf_eq_bot {K : Subgroup A} (hc : Subgroup.center ↥K = ⊥) : centerOf K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h := (mem_centerOf_iff (x := ⟨x, hx.1⟩)).1 hx
  rw [hc] at h
  exact congrArg Subtype.val (Subgroup.mem_bot.1 h)

theorem exists_flag {K Y : Subgroup A} {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hc : Subgroup.center ↥K = ⊥)
    (ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hψ : Function.Bijective ψ)
    (hpar : IsParabolic2 K Y) (hYK : Y ≠ K) (hne : perfectCore Y ≠ ⊥) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (I : Set ℕ) (a m : ℕ) (_ : a + m ≤ n),
      3 ≤ m ∧ (a = 0 ∨ a ∈ I) ∧ (a + m = n ∨ a + m ∈ I) ∧ (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) ∧
      (∀ c ∈ I, 1 ≤ c ∧ c < n) ∧ (0 < a ∨ a + m < n) ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) Y = flagStabilizer n (ZMod 2) I ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) (perfectCore Y) =
        perfectCore (flagStabilizer n (ZMod 2) I) := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := centerOf_eq_bot hc
  obtain ⟨hYK', S, hS, hSY⟩ := hpar
  have hSY' : S ≤ Y := fun s hs => hSY ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  have hker : ψ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).2 hψ.1]
    exact bot_le
  have hSsyl := isSylowTwoOf_img hker hψ.2 hS (hZ ▸ bot_le)
  obtain ⟨Pu, hPu⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hUsyl : IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    hPu ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Pu
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hUsyl hSsyl
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ
  have hθi : Function.Injective θ := (MulAut.conj g⁻¹).injective.comp hψ.1
  have hθker : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθi]
    exact bot_le
  have hθS : img θ S = unitriangular n (ZMod 2) := by
    rw [img, hθ, ← Subgroup.map_map, ← img, ← hg, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (SpecialLinearGroup (Fin n) (ZMod 2)) := by
      ext x : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  have hUQ : upperTriangular n (ZMod 2) ≤ img θ Y := by
    refine (upperTriangular_le_unitriangular hK2).trans ?_
    rw [← hθS]
    exact Subgroup.map_mono fun x hx => hSY' hx
  obtain ⟨hQI, -⟩ := borel_overgroups (img θ Y) hUQ
  set I := borelOvergroupCuts (img θ Y) with hI
  have hIcuts : ∀ c ∈ I, 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  have hQtop : img θ Y ≠ ⊤ := img_ne_top hθker hYK' (hZ ▸ bot_le) hYK
  have hMQ : img θ (perfectCore Y) = perfectCore (img θ Y) := img_perfectCore θ hYK'
  have hMne : perfectCore (img θ Y) ≠ ⊥ := by
    rw [← hMQ]
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := (perfectCore_le Y).trans hYK' hx
    have h1 : θ ⟨x, hxK⟩ ∈ img θ (perfectCore Y) := ⟨⟨x, hxK⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxK⟩ : ↥K) = 1 := hθi (h1.trans (map_one θ).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    apply hMne
    rw [hQI]
    exact perfectCore_eq_bot_of_small hK2 (by omega) hsmall
  have hmn : m < n := by
    by_contra hmn
    apply hQtop
    have hIe : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨h1, h2⟩ := hIcuts c hc
      exact hno c hc ⟨by omega, by omega⟩
    rw [hQI, hIe, flagStabilizer_empty]
  exact ⟨g, I, a, m, h, hm3, ha, hb, hno, hIcuts, by omega, hQI, hMQ.trans (congrArg _ hQI)⟩

theorem l45_config {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hc : Subgroup.center ↥K = ⊥)
    (hM₀K : M₀ ≤ K) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hψ : Function.Bijective ψ) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n)
      (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)),
      3 ≤ m ∧ (a = 0 ∨ a ∈ I) ∧ (a + m = n ∨ a + m ∈ I) ∧ (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) ∧
      (∀ c ∈ I, 1 ≤ c ∧ c < n) ∧ (0 < a ∨ a + m < n) ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) Y = flagStabilizer n (ZMod 2) I ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) M₀ =
        perfectCore (flagStabilizer n (ZMod 2) I) ∧
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥M₀ ∧
      (∀ x : ↥M₀,
        blkAt a m h (((MulAut.conj g⁻¹).toMonoidHom.comp ψ ⟨x, hM₀K x.2⟩ :
          SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
            ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) ∧
        BlockForm a m (((MulAut.conj g⁻¹).toMonoidHom.comp ψ ⟨x, hM₀K x.2⟩ :
          SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) ∧
      (∀ (k l : Fin n) (hkl : IsCross a m k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
        (MulAut.conj g⁻¹).toMonoidHom.comp ψ ⟨p, hM₀K p.2⟩ =
          SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2)) := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, I, a, m, h, hm3, ha, hb, hno, hIc, hprop, hQ, hM⟩ :=
    exists_flag hn4 hn5 hc ψ hψ hD.parabolic hD.ne_top (hD.eq_perfectCore ▸ hD.ne_bot)
  rw [← hD.eq_perfectCore] at hM
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ
  have hθi : Function.Injective θ := (MulAut.conj g⁻¹).injective.comp hψ.1
  have hθmem : ∀ x : ↥M₀, θ ⟨x, hM₀K x.2⟩ ∈ perfectCore (flagStabilizer n (ZMod 2) I) :=
    fun x => hM ▸ ⟨⟨x, hM₀K x.2⟩, x.2, rfl⟩
  set α' : ↥M₀ →* ↥(perfectCore (flagStabilizer n (ZMod 2) I)) :=
    (θ.comp (Subgroup.inclusion hM₀K)).codRestrict _ hθmem with hα'
  have hα'v : ∀ x, ((α' x : ↥(perfectCore (flagStabilizer n (ZMod 2) I))) :
      SpecialLinearGroup (Fin n) (ZMod 2)) = θ ⟨x, hM₀K x.2⟩ := fun x => rfl
  have hα's : Function.Surjective α' := by
    rintro ⟨y, hy⟩
    rw [← hM] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  set bb := bigBlockHom (K := ZMod 2) I a m h ha hb with hbb
  have hbbs : Function.Surjective bb := bigBlockHom_surjective hK2 h hm3 ha hb hno
  set α := bb.comp α' with hα
  have hαs : Function.Surjective α := hbbs.comp hα's
  have hker2 : IsPGroup 2 ↥α.ker := by
    rintro ⟨x, hx⟩
    have hU := unitriangular_of_bigBlockHom hK2 hn5 h hm3 ha hb hno (α' x) hx
    obtain ⟨j, hj⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) (by omega) ⟨_, hU⟩
    have hj' : θ ⟨x, hM₀K x.2⟩ ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa [hα'v] using this
    have h1 : θ (⟨x, hM₀K x.2⟩ ^ 2 ^ j) = θ 1 := by rw [map_pow, hj', map_one]
    have h2 := hθi h1
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val h2
    simpa using this
  have hsimp := sl_isSimple_of_card_two hK2 hm3
  have hnab := sl_nonabelian_of_card_two hK2 hm3
  have hkerα : α.ker = CFSG.pCore 2 ↥M₀ := (pCore_two_eq_ker hnab α hαs hker2).symm
  refine ⟨g, I, a, m, h, α, hm3, ha, hb, hno, hIc, hprop, hQ, hM, hαs, hkerα,
    fun x => ⟨?_, ?_⟩, fun k l hkl => ?_⟩
  · exact (bigBlockHom_coe I a m h ha hb (α' x)).symm
  · exact blockForm_of_mem hn5 h hm3 ha hb (hθmem x)
  · obtain ⟨p, hp⟩ := hα's ⟨_, transvection_mem_perfectCore h hm3 hno hkl⟩
    refine ⟨p, ?_, ?_⟩
    · rw [← hkerα, MonoidHom.mem_ker]
      show bb (α' p) = 1
      rw [hp]
      apply Subtype.ext
      rw [bigBlockHom_coe]
      exact blkAt_transvection_cross h hkl
    · rw [← hα'v, hp]

end CFSG.Quasithin.C35Pf
