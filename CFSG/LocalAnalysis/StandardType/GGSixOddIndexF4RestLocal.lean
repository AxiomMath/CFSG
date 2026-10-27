module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

namespace F4Rest

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (Y : Subgroup G)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf Y) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE Y

theorem isElemAbelian_comap {H : Type*} [Group H] {ψ : H →* G} (hψ : Function.Injective ψ)
    {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) : IsElemAbelian p (B.comap ψ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩, fun x hx => hψ ?_⟩
  · change ψ ((a : H) * b) = ψ ((b : H) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
  · rw [map_pow, hB.2 _ hx, map_one]

theorem card_map_conj (g : G) (E : Subgroup G) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_eq_mul_of_existsUnique {P Q M : Subgroup G} (hQ : Q ≤ P) (hM : M ≤ P)
    (h : ∀ g ∈ P, ∃! qm : G × G, qm.1 ∈ Q ∧ qm.2 ∈ M ∧ g = qm.1 * qm.2) :
    Nat.card P = Nat.card Q * Nat.card M := by
  let f : Q × M → P := fun qm => ⟨qm.1 * qm.2, mul_mem (hQ qm.1.2) (hM qm.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun g => ?_⟩
    · have hab' : (a.1 : G) * a.2 = b.1 * b.2 := congrArg Subtype.val hab
      obtain ⟨qm, -, huniq⟩ := h ((a.1 : G) * a.2) (mul_mem (hQ a.1.2) (hM a.2.2))
      have h1 := huniq ((a.1 : G), (a.2 : G)) ⟨a.1.2, a.2.2, rfl⟩
      have h2 := huniq ((b.1 : G), (b.2 : G)) ⟨b.1.2, b.2.2, hab'⟩
      have h3 := h1.trans h2.symm
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h3)) (Subtype.ext (congrArg Prod.snd h3))
    · obtain ⟨qm, ⟨hq, hm, he⟩, -⟩ := h g g.2
      exact ⟨(⟨qm.1, hq⟩, ⟨qm.2, hm⟩), Subtype.ext he.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem exists_conj_le_of_card_eq_mul [Finite G] {p : ℕ} [Fact p.Prime] {P Q M F : Subgroup G}
    (hMP : M ≤ P) (hcard : Nat.card P = Nat.card Q * Nat.card M) (hQ : ¬ p ∣ Nat.card Q)
    (hFP : F ≤ P) (hF : IsPGroup p F) :
    ∃ x ∈ P, F.map (MulAut.conj x).toMonoidHom ≤ M := by
  set M' := M.subgroupOf P
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p M'))
  set T' : Subgroup P := (T : Subgroup M').map M'.subtype
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hcardT' : Nat.card T' = Nat.card T :=
    Subgroup.card_map_of_injective M'.subtype_injective
  have hM' : Nat.card M' = Nat.card M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMP).toEquiv
  have h1 := Subgroup.card_mul_index T'
  have h2 := Subgroup.card_mul_index (T : Subgroup M')
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hidx : T'.index = Nat.card Q * (T : Subgroup M').index := by
    have e : Nat.card T' * T'.index = Nat.card T' * (Nat.card Q * (T : Subgroup M').index) := by
      calc Nat.card T' * T'.index = Nat.card P := h1
        _ = Nat.card Q * Nat.card M' := by rw [hcard, hM']
        _ = Nat.card Q * (Nat.card T * (T : Subgroup M').index) := by rw [h2]
        _ = Nat.card T' * (Nat.card Q * (T : Subgroup M').index) := by rw [hcardT']; ring
    exact Nat.eq_of_mul_eq_mul_left (hcardT' ▸ hTpos) e
  have hnd : ¬ p ∣ T'.index := by
    rw [hidx]
    intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hd with h | h
    · exact hQ h
    · exact T.not_dvd_index h
  set S' : Sylow p P := hT'p.toSylow hnd
  have hF' : IsPGroup p (F.subgroupOf P) := hF.comap_of_injective P.subtype P.subtype_injective
  obtain ⟨S'', hFS''⟩ := hF'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq P S'' S'
  refine ⟨(y : G), y.2, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  have hfP : f ∈ P := hFP hf
  have hmem : (MulAut.conj y).toMonoidHom ⟨f, hfP⟩ ∈ ((y • S'' : Sylow p P) : Subgroup P) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hFS'' (show (⟨f, hfP⟩ : P) ∈ F.subgroupOf P from Subgroup.mem_subgroupOf.2 hf) using 1
    simp only [MulAut.smul_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  rw [hy] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have htM : ((t : M') : G) ∈ M := t.2
  have e : ((t : M') : G) = (y : G) * f * (y : G)⁻¹ := congrArg Subtype.val hte
  change (y : G) * f * (y : G)⁻¹ ∈ M
  rw [← e]
  exact htM

theorem pow_mem_of_mem_sup {H L : Subgroup G} (hHL : H ≤ Subgroup.normalizer (L : Set G))
    {n : ℕ} (hH : ∀ h ∈ H, h ^ n = 1) {x : G} (hx : x ∈ L ⊔ H) : x ^ n ∈ L := by
  have hx' : x ∈ (L : Set G) * (H : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L H hHL]
    exact hx
  obtain ⟨l, hl, h, hh, rfl⟩ := hx'
  have key : ∀ k : ℕ, ∃ l' ∈ L, (l * h) ^ k = l' * h ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hconj : h ^ k * l * (h ^ k)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (pow_mem (hHL hh) k) l).1 hl
      refine ⟨l' * (h ^ k * l * (h ^ k)⁻¹), mul_mem hl' hconj, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨l', hl', he⟩ := key n
  rw [he, hH h hh, mul_one]
  exact hl'

theorem mem_of_mem_sup_of_pow_eq_one {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hH : ∀ h ∈ H, h ^ n = 1) {x : G} (hx : x ∈ L ⊔ H) (hxp : x ^ p = 1) : x ∈ L := by
  have hcop : Nat.Coprime n p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hxk : x = (x ^ n) ^ k := by
    rw [← pow_mul, ← Nat.mod_add_div (n * k) p, pow_add, pow_mul, hxp, one_pow, mul_one, hk,
      pow_one]
  rw [hxk]
  exact pow_mem (pow_mem_of_mem_sup hHL hH hx) k

end General

section F4

variable {K : Type} [Field K]

@[expose] def GGF4LeviRankInput (K : Type) [Field K]
    (p : ℕ) : Prop :=
  ∀ i : Fin Tag.F4.rank, ∀ E : Subgroup (ModGL .F4 K),
    E ≤ subsystemGroup .F4 K {j | j ≠ i} → IsElemAbelian p E → Nat.card E ≤ p ^ 3

theorem pow_card_sub_one_eq_one_of_mem_torusGroup
    [Finite K] {h : ModGL .F4 K} (hh : h ∈ torusGroup .F4 K) :
    h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [rootDiagUnit_pow, ← rootDiagUnit_one]
  congr 1
  funext j
  rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
  exact pow_card_eq_one'

theorem twoLocal_card_le_of_levi
    [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) (hL : GGF4LeviRankInput K p)
    {R E : Subgroup (adjointGroup .F4 K)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set (adjointGroup .F4 K))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  have := Fact.mk Nat.prime_two
  have := Fact.mk hp
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨S, P, hPtop, hNP, -, -, hSP⟩ := holds_adjointGroup_tag .F4 K 2 R hR hR2
  have hBC : borelGroup .F4 K ≤ (adjointGroup .F4 K) := borelGroup_le_adjointGroup'
  have hUC : posUnipotent .F4 K ≤ (adjointGroup .F4 K) := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .F4 K) (hUp.toSylow hUi) S
  have hBN : borelGroup .F4 K ≤ Subgroup.normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) :=
    sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) Subgroup.le_normalizer
  have hB₀N : (borelGroup .F4 K).subgroupOf (adjointGroup .F4 K) ≤
      Subgroup.normalizer (((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K) :
        Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := Subgroup.mem_normalizer_iff.1 (hBN (Subgroup.mem_subgroupOf.1 hb)) (u : ModGL .F4 K)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hSeq : (S : Subgroup (adjointGroup .F4 K)) =
      ((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
  have hB₀P' : (borelGroup .F4 K).subgroupOf (adjointGroup .F4 K) ≤ P' := by
    intro b hb
    have h1 : (MulAut.conj g).toMonoidHom b ∈ P := by
      apply hSP
      rw [hSeq]
      exact Subgroup.le_normalizer_map _ ⟨b, hB₀N hb, rfl⟩
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set A := P'.map (adjointGroup .F4 K).subtype with hAdef
  have hBA : borelGroup .F4 K ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hB₀P' (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hAC : A ≤ (adjointGroup .F4 K) := Subgroup.map_le_iff_le_comap.2 fun x _ => x.2
  have hAJ := (borel_overgroup_classification .F4 K).1 A hBA hAC
  set J : Set (Fin Tag.F4.rank) := {i | weylElt .F4 K i 1 ∈ A} with hJdef
  have hcells := standard_parabolic_cells .F4 K
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    apply hPtop
    have hJu : J = Set.univ := Set.eq_univ_of_forall hall
    have hAtop : A = (adjointGroup .F4 K) := by rw [hAJ, hJu, hcells.2.2.2.2.2.1]
    have hP'top : P' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL .F4 K) ∈ A := by rw [hAtop]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Subtype.ext hyx] at hy
      exact hy
    rw [eq_top_iff]
    intro x _
    have hx : (MulAut.conj g⁻¹).toMonoidHom x ∈ P' := by rw [hP'top]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g⁻¹).injective hyx
    rw [← this]
    exact hy
  set J₀ : Set (Fin Tag.F4.rank) := {j | j ≠ i} with hJ₀def
  have hJJ₀ : J ⊆ J₀ := fun j hj hji => hi (hji ▸ hj)
  have hAP : A ≤ parabolicSubgroup .F4 K J₀ := by
    rw [hAJ]
    exact (hcells.2.2.2.1 J J₀).2 hJJ₀
  set F := (E.map (MulAut.conj g⁻¹).toMonoidHom).map (adjointGroup .F4 K).subtype with hFdef
  have hFA : F ≤ A := Subgroup.map_mono (Subgroup.map_mono (hER.trans hNP))
  have hFcard : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective, card_map_conj]
  have hFel : IsElemAbelian p F := isElemAbelian_map _ (isElemAbelian_map _ hE)
  obtain ⟨hQP, -, -, hMP, -, -, huniq, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors (τ := .F4) (K := K) J₀
  obtain ⟨-, hQ2, -⟩ := hfin 2
  have hcard := card_eq_mul_of_existsUnique hQP hMP huniq
  have hQp : ¬ p ∣ Nat.card (parabolicRadical .F4 K J₀) := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨x, -, hxM⟩ := exists_conj_le_of_card_eq_mul hMP hcard hQp (hFA.trans hAP)
    (isPGroup_of_isElemAbelian hFel)
  set F' := F.map (MulAut.conj x).toMonoidHom with hF'def
  have hF'el : IsElemAbelian p F' := isElemAbelian_map _ hFel
  have hF'L : F' ≤ subsystemGroup .F4 K J₀ := by
    intro y hy
    have hyM : y ∈ subsystemGroup .F4 K J₀ ⊔ torusGroup .F4 K := by
      rw [sup_comm]
      exact hxM hy
    exact mem_of_mem_sup_of_pow_eq_one (RootCentExc.torusGroup_le_normalizer_leviGens J₀) hp hpq
      (fun h hh => pow_card_sub_one_eq_one_of_mem_torusGroup hh) hyM (hF'el.2 y hy)
  calc Nat.card E = Nat.card F' := by rw [card_map_conj, hFcard]
    _ ≤ p ^ 3 := hL i F' hF'L hF'el

end F4

section Main

theorem ggF4TwoLocalRankInput_of_levi
    (hL : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card K - 1 → GGF4LeviRankInput K p) : GGF4TwoLocalRankInput := by
  intro G _ _ n f ψ G₀ hcfg p hp hp2 hpq R hRG hR hR2 E hEG hER hE
  obtain ⟨-, -, hrange, hker, -, -, -⟩ := hcfg
  subst hrange
  have hψ := ggF4_injective_of_center_eq_bot center_adjointGroup_eq_bot hker
  have hf : f ≠ 0 := by
    rintro rfl
    exact hpq (by simp)
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hpq' : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have hR' : R.comap ψ ≠ ⊥ := by
    intro h
    apply hR
    rw [← Subgroup.map_comap_eq_self hRG, h, Subgroup.map_bot]
  have hE'R' : E.comap ψ ≤ Subgroup.normalizer ((R.comap ψ : Subgroup _) : Set _) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have h := Subgroup.mem_normalizer_iff.1 (hER he) (ψ r)
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact h
  have hcardE : Nat.card (E.comap ψ) = Nat.card E := by
    calc Nat.card (E.comap ψ) = Nat.card ((E.comap ψ).map ψ) :=
          (Subgroup.card_map_of_injective hψ).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEG]
  rw [← hcardE]
  exact twoLocal_card_le_of_levi (K := GaloisField 2 f) hp hp2 hpq'
    (hL (GaloisField 2 f) p hp hp2 hpq') hR' (hR2.comap_of_injective ψ hψ) hE'R'
    (isElemAbelian_comap hψ hE)

end Main

end F4Rest

end CFSG.StandardType
