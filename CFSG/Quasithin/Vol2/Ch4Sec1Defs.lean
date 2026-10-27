module

public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

section Defs

variable {G : Type} [Group G]

structure Hyp4_1_1 (G : Type) [Group G] [Finite G] (T M Mp : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  T_le : T ≤ M
  oTwoUpper_eq : oTwoUpper Mp = Mp
  Mp_le : Mp ≤ M
  normal : M ≤ Subgroup.normalizer (Mp : Set G)
  unique : ∀ I : Subgroup G, I ≤ M →
    Mp ⊔ (T ⊓ centralizerSection M Mp (pCoreOf 2 Mp)) ≤ I →
    centralizerSection M Mp (pCoreOf 2 Mp) ⊔ I = M → IsUniqueM I M

@[expose] def IsSigma (M Mp Mm : Subgroup G) : Prop :=
  Mm ≤ M ∧ Mp ⊔ centralizerSection M Mp (pCoreOf 2 Mp) ≤ Mm

@[expose] def IsIota (M Mp Mm I : Subgroup G) : Prop :=
  I ≤ Mm ∧ I ⊔ centralizerSection M Mp (pCoreOf 2 Mp) = Mm ∧ Mp ≤ I ⊔ pCoreOf 2 Mp ∧
    pCoreOf 2 I ≠ ⊥

@[expose] def IsGamma (M Mp Mm I : Subgroup G) : Prop :=
  IsIota M Mp Mm I ∧ ∃ H : Subgroup G, InH I H ∧ ¬ H ≤ M

@[expose] def OrdLE (Mp I₁ I₂ : Subgroup G) : Prop :=
  pCoreOf 2 I₁ ≤ pCoreOf 2 I₂ ∧ I₁ ⊓ Mp ≤ I₂ ⊓ Mp

@[expose] def IsGammaStar (M Mp Mm I : Subgroup G) : Prop :=
  IsGamma M Mp Mm I ∧
    ∀ I₁ : Subgroup G, IsGamma M Mp Mm I₁ → OrdLE Mp I I₁ → ¬ pCoreOf 2 I < pCoreOf 2 I₁

end Defs

section Conj

variable {G : Type} [Group G]

theorem mem_map_conj_iff {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_le_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨k, hk, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hg k).mp hk

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  refine le_antisymm (map_conj_le_of_mem_normalizer hg) fun x hx => ?_
  rw [mem_map_conj_iff]
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  simpa using this

theorem map_conj_mono {K L : Subgroup G} (h : K ≤ L) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_mono h

theorem map_conj_inv_map_conj (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  ext x
  rw [mem_map_conj_iff, inv_inv, mem_map_conj_iff]
  simp [mul_assoc]

theorem map_conj_map_conj_inv (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  have := map_conj_inv_map_conj K g⁻¹
  rwa [inv_inv] at this

theorem isTwoLocal_map_conj {M : Subgroup G} (hM : IsTwoLocal M) (g : G) :
    IsTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  · exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)

theorem isMaxTwoLocal_map_conj {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) (g : G) :
    quasithinIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isTwoLocal_map_conj hM.1 g, fun H hH hle => ?_⟩
  have h1 : M ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rwa [map_conj_inv_map_conj] at this
  have h2 := hM.2 _ (isTwoLocal_map_conj hH g⁻¹) h1
  have h3 := congrArg (fun K : Subgroup G => K.map (MulAut.conj g).toMonoidHom) h2
  rw [← h3, map_conj_map_conj_inv]

theorem isUniqueM_map_conj {X M : Subgroup G} (hU : IsUniqueM X M) {g : G} (hg : g ∈ M) :
    IsUniqueM (X.map (MulAut.conj g).toMonoidHom) M := by
  have hgM : g ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hg
  refine ⟨⟨hU.1.1, ?_⟩, fun M' hM' => ?_⟩
  · exact (map_conj_mono hU.1.2 g).trans (map_conj_le_of_mem_normalizer hgM)
  · have h1 : X ≤ M'.map (MulAut.conj g⁻¹).toMonoidHom := by
      have := map_conj_mono hM'.2 g⁻¹
      rwa [map_conj_inv_map_conj] at this
    have h2 := hU.2 _ ⟨isMaxTwoLocal_map_conj hM'.1 g⁻¹, h1⟩
    have h3 := congrArg (fun K : Subgroup G => K.map (MulAut.conj g).toMonoidHom) h2
    simp only [map_conj_map_conj_inv] at h3
    rw [h3]
    exact map_conj_eq_of_mem_normalizer hgM

theorem isUniqueM_mono {X X' M : Subgroup G} (hU : IsUniqueM X M) (hXX : X ≤ X') (hX' : X' ≤ M) :
    IsUniqueM X' M :=
  ⟨⟨hU.1.1, hX'⟩, fun M' hM' => hU.2 M' ⟨hM'.1, hXX.trans hM'.2⟩⟩

theorem isUniqueM_le_of_isTwoLocal [Finite G] {X M H : Subgroup G} (hU : IsUniqueM X M)
    (hH : IsTwoLocal H) (hXH : X ≤ H) : H ≤ M := by
  obtain ⟨M', hM', hHM'⟩ := exists_maxTwoLocal_ge hH
  rw [← hU.2 M' ⟨hM', hXH.trans hHM'⟩]
  exact hHM'

theorem isUniqueM_normalizer_le [Finite G] {X M P : Subgroup G} (hU : IsUniqueM X M)
    (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) (hXP : X ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ M :=
  isUniqueM_le_of_isTwoLocal hU ⟨P, hP, hP2, rfl⟩ hXP

theorem isUniqueM_le_of_inH [Finite G] {X M H : Subgroup G} (hU : IsUniqueM X M)
    (hH : InH X H) : H ≤ M :=
  (le_normalizer_pCoreOf 2 H).trans (isUniqueM_normalizer_le hU hH.2 (pCoreOf_isPGroup 2 H)
    (hH.1.trans (le_normalizer_pCoreOf 2 H)))

end Conj

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_map_conj {S H : Subgroup G} (hS : IsSylowTwoOf S H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) H := by
  rw [isSylowTwoOf_iff_maximal] at hS ⊢
  obtain ⟨hSH, hS2, hmax⟩ := hS
  refine ⟨(map_conj_mono hSH g).trans (map_conj_le_of_mem_normalizer hg), hS2.map _,
    fun P hPH hP2 hSP => ?_⟩
  have h1 : S ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := map_conj_mono hSP g⁻¹
    rwa [map_conj_inv_map_conj] at this
  have h2 := hmax _ ((map_conj_mono hPH g⁻¹).trans
    (map_conj_le_of_mem_normalizer (inv_mem hg))) (hP2.map _) h1
  have h3 := map_conj_mono h2 g
  rwa [map_conj_map_conj_inv] at h3

theorem sup_inf_normalizer_eq {M N P : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hP : IsSylowTwoOf P N) :
    N ⊔ M ⊓ Subgroup.normalizer (P : Set G) = M := by
  refine le_antisymm (sup_le hNM inf_le_left) fun m hm => ?_
  have hPm := isSylowTwoOf_map_conj hP (hMN hm)
  obtain ⟨n, hn, hnP⟩ := exists_conj_of_isSylowTwoOf hP hPm
  have hnm : n⁻¹ * m ∈ M ⊓ Subgroup.normalizer (P : Set G) := by
    refine ⟨M.mul_mem (M.inv_mem (hNM hn)) hm, ?_⟩
    show n⁻¹ * m ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : m * x * m⁻¹ ∈ P.map (MulAut.conj m).toMonoidHom := ⟨x, hx, rfl⟩
      have h2 := (hnP _).mp h1
      have e : n⁻¹ * m * x * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * x * m⁻¹) * n := by group
      rwa [e]
    · intro hx
      have e : n⁻¹ * (m * x * m⁻¹) * n = n⁻¹ * m * x * (n⁻¹ * m)⁻¹ := by group
      have h1 := (hnP (m * x * m⁻¹)).mpr (e ▸ hx)
      rw [mem_map_conj_iff] at h1
      simpa [mul_assoc] using h1
  have e : m = n * (n⁻¹ * m) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hnm)

end Sylow

end CFSG.Quasithin.H13.Ch4
