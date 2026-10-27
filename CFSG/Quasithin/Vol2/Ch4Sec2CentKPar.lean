module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinPar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L I H K : Subgroup G}

theorem exists_parabolicData' (c : Conf4212 G T M L I H K) {F : Type} [Field F]
    {V₁ : Subgroup G}
    (hstab : IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁) :
    ∃ (W : Subgroup G) (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥W →* Multiplicative (Fin 3 → F))
      (W' : Submodule F (Fin 3 → F)),
      W ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)), K⁆ ∧
      IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β ∧
      Module.finrank F W' = 2 ∧
      ((perfectCore (L ⊓ H)).subgroupOf K).map α ≠ ⊥ ∧
      ⁅((perfectCore (L ⊓ H)).subgroupOf K).map α,
        ((perfectCore (L ⊓ H)).subgroupOf K).map α⁆ =
        ((perfectCore (L ⊓ H)).subgroupOf K).map α ∧
      (∀ y ∈ ((perfectCore (L ⊓ H)).subgroupOf K).map α, ∀ w ∈ W',
        (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') ∧
      (∀ g : ↥(StatedSL 3 F),
        (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
          g ∈ Subgroup.normalizer
            ((((perfectCore (L ⊓ H)).subgroupOf K).map α : Subgroup ↥(StatedSL 3 F)) :
              Set ↥(StatedSL 3 F))) := by
  obtain ⟨W, hWle, α', β', hnat, hline1, hMK⟩ := hstab
  have hnat₀ := hnat
  obtain ⟨hKW, hα', hkerα', hβ', -, hequiv'⟩ := hnat
  obtain ⟨hV1W, W', hW', hW'iff⟩ := hline1
  have hLHK : perfectCore (L ⊓ H) ≤ K := c.LH_le
  have hLHN : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (V₁ : Set G) := by
    have : perfectCore (L ⊓ H) ≤ H ⊓ M ⊓ K := le_inf (le_of_mem_cComp c.LH_mem) hLHK
    rw [hMK] at this
    exact this.trans inf_le_right
  set A₀ := (perfectCore (L ⊓ H)).subgroupOf K with hA₀
  have hA₀map : A₀.map K.subtype = perfectCore (L ⊓ H) := by
    rw [hA₀, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hLHK
  have hLHperf : ⁅perfectCore (L ⊓ H), perfectCore (L ⊓ H)⁆ = perfectCore (L ⊓ H) :=
    perfectCore_perfect _
  have hA₀perf : ⁅A₀, A₀⁆ = A₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hA₀map, hLHperf]
  set Y₀ := A₀.map α' with hY₀
  have hY₀perf : ⁅Y₀, Y₀⁆ = Y₀ := by rw [hY₀, ← Subgroup.map_commutator, hA₀perf]
  have hstab₀ : ∀ y ∈ Y₀, ∀ w ∈ W',
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W' := by
    rintro _ ⟨l, hl, rfl⟩ w hw
    obtain ⟨u, hu⟩ := hβ' (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V₁ := (hW'iff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    have hlN : (l : G) ∈ Subgroup.normalizer (V₁ : Set G) := hLHN hl
    let v : ↥W := ⟨l * u * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW l.2) u).mp u.2⟩
    have h1 := hequiv' l u v rfl
    rw [hu, toAdd_ofAdd] at h1
    have h2 : (v : G) ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hlN u).mp huV
    have h3 := (hW'iff v).mp h2
    rw [h1] at h3
    exact h3
  have hY₀ne : Y₀ ≠ ⊥ := by
    intro hbot
    apply ne_bot_of_mem_cComp c.LH_mem
    apply eq_bot_of_perfect_of_isPGroup_two hLHperf
    refine (pCoreOf_isPGroup 2 K).to_le ?_
    intro l hl
    have h1 : α' ⟨l, hLHK hl⟩ ∈ Y₀ := ⟨⟨l, hLHK hl⟩, hl, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨l, hLHK hl⟩ : ↥K) ∈ α'.ker := h1
    rw [hkerα'] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hPnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
        g ∈ Subgroup.normalizer ((Y₀ : Subgroup ↥(StatedSL 3 F)) : Set ↥(StatedSL 3 F)) := by
    intro g hg
    obtain ⟨k', rfl⟩ := hα' g
    have hk'V : (k' : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ W := hV1W hv
      let vW : ↥W := ⟨v, hvW⟩
      let v' : ↥W := ⟨k' * v * (k' : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW k'.2) v).mp hvW⟩
      have h1 := hequiv' k' vW v' rfl
      have h2 : Multiplicative.toAdd (β' vW) ∈ W' := (hW'iff vW).mp hv
      exact (hW'iff v').mpr (by rw [h1]; exact hg _ h2)
    have hk'HM : (k' : G) ∈ H ⊓ M := by
      have : (k' : G) ∈ K ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨k'.2, hk'V⟩
      rw [← hMK] at this
      exact this.1
    have hk'L : (k' : G) ∈ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
      c.LH_normal hk'HM
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨k' * l * k'⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hk'L l).mp hl
    · rintro ⟨l, hl, hle⟩
      refine ⟨k'⁻¹ * l * k', ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk'L) l).mp hl
        rw [inv_inv] at this
        exact this
      · rw [map_mul, map_mul, map_inv, hle]
        group
  exact ⟨W, α', β', W', hWle, hnat₀, hW', hY₀ne, hY₀perf, hstab₀, hPnorm⟩

theorem exists_pCoreOf_LH_not_le (c : Conf4212 G T M L I H K) {F : Type} [Field F] [Fintype F]
    (hF : ∃ m : ℕ, 2 ≤ m ∧ Fintype.card F = 2 ^ m) {V₁ : Subgroup G}
    (hstab : IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁) :
    ∃ g ∈ pCoreOf 2 (perfectCore (L ⊓ H)), g ∉ pCoreOf 2 K := by
  obtain ⟨_W, α, _β, W', -, hnat, hW', hY₀ne, hY₀perf, hstab₀, hPnorm⟩ :=
    exists_parabolicData' c hstab
  obtain ⟨-, -, hkerα, -, -, -⟩ := hnat
  obtain ⟨m, hm, hFm⟩ := hF
  have hLHK : perfectCore (L ⊓ H) ≤ K := c.LH_le
  set LH := perfectCore (L ⊓ H) with hLH
  set A₀ := LH.subgroupOf K with hA₀
  set Y₀ := A₀.map α with hY₀
  obtain ⟨N, hN0, hNY, hNsq, hNconj⟩ :=
    exists_normal_elemAbelian_of_planeStab hm hFm W' hW' Y₀ hY₀ne hY₀perf hstab₀ hPnorm
  set S : Subgroup ↥K := N.comap α ⊓ A₀ with hS
  set P : Subgroup G := S.map K.subtype with hP
  have hPmem : ∀ s : ↥K, s ∈ S → (s : G) ∈ P := fun s hs => Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hPle : P ≤ LH := by
    rintro _ hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hs).2
  have hLHP : LH ≤ Subgroup.normalizer (P : Set G) := by
    intro l hl
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hlK : l ∈ K := hLHK hl
    have hl' : (⟨l, hlK⟩ : ↥K) ∈ A₀ := Subgroup.mem_subgroupOf.mpr hl
    obtain ⟨hsN, hsA⟩ := Subgroup.mem_inf.mp hs
    have hαs : α s ∈ N := hsN
    have hy : α ⟨l, hlK⟩ ∈ Y₀ := Subgroup.mem_map.mpr ⟨_, hl', rfl⟩
    have ht : (⟨l, hlK⟩ : ↥K) * s * (⟨l, hlK⟩ : ↥K)⁻¹ ∈ S := by
      refine Subgroup.mem_inf.mpr ⟨?_, A₀.mul_mem (A₀.mul_mem hl' hsA) (A₀.inv_mem hl')⟩
      show α ((⟨l, hlK⟩ : ↥K) * s * (⟨l, hlK⟩ : ↥K)⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNconj _ hy _ hαs
    exact hPmem _ ht
  have hP2 : IsPGroup 2 ↥P := by
    intro x
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨hsN, -⟩ := Subgroup.mem_inf.mp hs
    have hαs : α s ∈ N := hsN
    have hss : s * s ∈ CFSG.pCore 2 ↥K := by
      rw [← hkerα, MonoidHom.mem_ker, map_mul]
      exact hNsq _ hαs
    have hgg : (s : G) * (s : G) ∈ pCoreOf 2 K := (mem_pCoreOf_iff' (s * s)).mpr hss
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 K ⟨(s : G) * (s : G), hgg⟩
    have hj' : ((s : G) * (s : G)) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hxs : (x : G) = (s : G) := hsx.symm
    refine ⟨j + 1, Subtype.ext ?_⟩
    have e : (s : G) ^ 2 ^ (j + 1) = ((s : G) * (s : G)) ^ 2 ^ j := by
      rw [← sq, ← pow_mul]
      congr 1
      ring
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hxs, e, hj']
  have hPPLH : P ≤ pCoreOf 2 LH := le_pCoreOf_of_le_normalizer 2 hPle hLHP hP2
  obtain ⟨n, hnN, hn1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one N).mp ((Subgroup.nontrivial_iff_ne_bot N).mpr hN0)
  obtain ⟨a, haA, hαa⟩ := Subgroup.mem_map.mp (hNY hnN)
  have haN : α a ∈ N := by rw [hαa]; exact hnN
  have haS : a ∈ S := Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr haN, haA⟩
  refine ⟨(a : G), hPPLH (hPmem a haS), fun hcore => ?_⟩
  have hak : a ∈ CFSG.pCore 2 ↥K := (mem_pCoreOf_iff' a).mp hcore
  have hker : α a = 1 := by
    have : a ∈ α.ker := by rw [hkerα]; exact hak
    exact MonoidHom.mem_ker.mp this
  exact hn1 (hαa.symm.trans hker)

end CFSG.Quasithin.H13.Ch4.CentK
