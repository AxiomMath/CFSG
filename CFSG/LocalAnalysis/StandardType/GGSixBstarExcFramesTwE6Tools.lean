module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveSylowGroup
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcFrames

open scoped Pointwise

theorem exists_conj_map_eq_of_SC {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {T X : Subgroup H} (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hXT : X ≤ T)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hTp : ∀ t ∈ T, t ^ p = 1 → t ∈ X)
    (hord : (Nat.card H).factorization p = (Nat.card T).factorization p + 1)
    (hcent : ∀ c : H, (∀ x ∈ X, c * x = x * c) → c ∈ T)
    (hfix : ∀ a ∈ Subgroup.normalizer (X : Set H), a ^ p = 1 →
      (∃ x ∈ X, a * x ≠ x * a) →
      Nat.card {x : X // a * (x : H) = (x : H) * a} < p ^ 3)
    {A : Subgroup H} (hA : CFSG.Open.IsElemAbelian p A) (hA4 : p ^ 4 ≤ Nat.card A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set H), c ^ p = 1 → c ∈ A) :
    ∃ c : H, X.map (MulAut.conj c).toMonoidHom = A := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hp_ne : p ≠ 0 := hp.ne_zero
  haveI : Finite T := Finite.of_injective Subtype.val Subtype.coe_injective
  have hXpg : IsPGroup p X := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by apply Subtype.ext; simpa using hXp x x.2⟩
  have hXpgT : IsPGroup p (X.comap T.subtype) := hXpg.comap_subtype
  obtain ⟨Q₀, hXQ₀⟩ := hXpgT.exists_le_sylow
  set Q : Subgroup H := Q₀.toSubgroup.map T.subtype with hQdef
  have hXQ : X ≤ Q := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hXT hx⟩, hXQ₀ hx, rfl⟩
  have hQT : Q ≤ T := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hQpg : IsPGroup p Q := Q₀.isPGroup'.map T.subtype
  obtain ⟨P, hQP⟩ := hQpg.exists_le_sylow
  have hcardP : Nat.card P = p ^ (Nat.card H).factorization p := Sylow.card_eq_multiplicity P
  have hcardQ0 : Nat.card Q₀ = p ^ (Nat.card T).factorization p := Sylow.card_eq_multiplicity Q₀
  have hcardQ : Nat.card Q = Nat.card Q₀ :=
    Subgroup.card_map_of_injective (K := Q₀.toSubgroup) (f := T.subtype) Subtype.coe_injective
  have hcardPQ : Nat.card P = p * Nat.card Q := by
    rw [hcardP, hord, pow_succ, hcardQ, hcardQ0]
    ring
  have hQrel : Q.relIndex P = p := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_eq_left.mpr hQP] at h
    rw [hcardPQ] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q)) h
  have hQindex : (Q.subgroupOf P).index = p := hQrel
  have hQn : (Q.subgroupOf P).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hQindex, hcardP, hord, Nat.Prime.pow_minFac hp (by omega)]
  have hPX : P ≤ Subgroup.normalizer (X : Set H) :=
    NoOffE8Five.le_normalizer_of_normal_subgroupOf_pow hQP hQn hQT hXQ hXp hTp
  have hApg : IsPGroup p A := hA.isPGroup
  obtain ⟨P', hAP'⟩ := hApg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P P'
  set A' : Subgroup H := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'def
  have hA'P : A' ≤ P := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
    have hc' : MulAut.conj c • (P : Subgroup H) = (P' : Subgroup H) := by
      rw [← Sylow.coe_subgroup_smul, hc]
    have haP' : a ∈ (P' : Subgroup H) := hAP' ha
    rw [← hc'] at haP'
    rcases (Subgroup.mem_smul_pointwise_iff_exists a (MulAut.conj c) P).mp haP' with
      ⟨q, hqP, hqa⟩
    have hq : MulAut.conj c⁻¹ a = q := by
      rw [← hqa, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    change MulAut.conj c⁻¹ a ∈ P
    rw [hq]
    exact hqP
  have hA'el : CFSG.Open.IsElemAbelian p A' := by
    rw [hA'def]
    exact CFSG.Open.IsElemAbelian.map hA _
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    simpa using congrArg (fun z : A' => (z : H)) (hA'el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA'card : p ^ 4 ≤ Nat.card A' := by
    rw [hA'def, Subgroup.card_map_of_injective (K := A)
      (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).injective]
    exact hA4
  have hSC' : ∀ x ∈ Subgroup.centralizer (A' : Set H), x ^ p = 1 → x ∈ A' := by
    intro x hx hxp
    set z : H := MulAut.conj c x with hz
    have hzC : ∀ a ∈ A, z * a = a * z := by
      intro a ha
      have hyA' : MulAut.conj c⁻¹ a ∈ A' := by
        rw [hA'def]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hyx : (MulAut.conj c⁻¹ a) * x = x * (MulAut.conj c⁻¹ a) :=
        (Subgroup.mem_centralizer_iff.mp hx) _ hyA'
      have hyx' : (c⁻¹ * a * c) * x = x * (c⁻¹ * a * c) := by
        simpa [MulAut.conj_apply] using hyx
      rw [hz, MulAut.conj_apply]
      calc c * x * c⁻¹ * a = c * (x * (c⁻¹ * a * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * a * c) * x) * c⁻¹ := by rw [← hyx']
        _ = a * (c * x * c⁻¹) := by group
    have hzp : z ^ p = 1 := by
      rw [hz, MulAut.conj_apply, conj_pow, hxp]
      group
    have hzA : z ∈ A :=
      hSC z (Subgroup.mem_centralizer_iff.mpr fun a ha => (hzC a ha).symm) hzp
    rw [hA'def]
    refine Subgroup.mem_map.mpr ⟨z, hzA, ?_⟩
    show MulAut.conj c⁻¹ z = x
    rw [hz, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hA'X : A' = X := by
    by_cases hcenX : ∀ a ∈ A', ∀ x ∈ X, a * x = x * a
    · have hA'T : A' ≤ T := by
        intro a ha
        exact hcent a (fun x hx => hcenX a ha x hx)
      have hA'Xle : A' ≤ X := fun a ha => hTp a (hA'T ha) (hA'el.2 a ha)
      have hXA' : X ≤ A' := by
        intro x hx
        exact hSC' x (Subgroup.mem_centralizer_iff.mpr fun a ha => hcenX a ha x hx)
          (hXp x hx)
      exact le_antisymm hA'Xle hXA'
    · push Not at hcenX
      obtain ⟨a, haA', x, hxX, hneq⟩ := hcenX
      have haN : a ∈ Subgroup.normalizer (X : Set H) := hPX (hA'P haA')
      have hap : a ^ p = 1 := hA'el.2 a haA'
      have hfixa := hfix a haN hap ⟨x, hxX, hneq⟩
      set B : Subgroup H := A' ⊓ Q with hBdef
      have hBX : B ≤ X := by
        intro b hb
        have hb' : (b : H) ∈ A' ⊓ Q := by rw [← hBdef]; exact hb
        exact hTp b (hQT hb'.2) (hA'el.2 b hb'.1)
      have hinj : Function.Injective
          (fun b : B => (⟨⟨b, hBX b.2⟩, by
            show a * (b : H) = (b : H) * a
            have hb' : (b : H) ∈ A' ⊓ Q := by rw [← hBdef]; exact b.2
            exact hA'comm a haA' (b : H) hb'.1⟩ :
              {x : X // a * (x : H) = (x : H) * a})) := by
        intro b₁ b₂ h
        apply Subtype.ext
        exact congrArg (fun y : {x : X // a * (x : H) = (x : H) * a} =>
          ((y.1 : X) : H)) h
      have hBcard : Nat.card B ≤
          Nat.card {x : X // a * (x : H) = (x : H) * a} :=
        Nat.card_le_card_of_injective _ hinj
      have hrelB : B.relIndex A' ≤ p := by
        rw [hBdef, Subgroup.inf_relIndex_left]
        exact (Subgroup.relIndex_le_of_le_right hA'P
          (by rw [hQrel]; exact hp_ne)).trans (le_of_eq hQrel)
      have hmul : B.relIndex A' * Nat.card B = Nat.card A' := by
        have h := Subgroup.relIndex_mul_card (H := B) (K := A')
        rwa [inf_eq_left.mpr (by rw [hBdef]; exact inf_le_left)] at h
      have hp3 : p ^ 3 ≤ Nat.card B := by
        have h := hA'card
        rw [← hmul] at h
        have hmul2 : p * p ^ 3 ≤ p * Nat.card B := by
          calc p * p ^ 3 = p ^ 4 := by ring
            _ ≤ B.relIndex A' * Nat.card B := h
            _ ≤ p * Nat.card B := Nat.mul_le_mul_right _ hrelB
        exact Nat.le_of_mul_le_mul_left hmul2 hp_pos
      exact absurd (le_trans hp3 hBcard) (not_le.mpr hfixa)
  refine ⟨c, ?_⟩
  rw [← hA'X, hA'def]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    have hxz : x = z := by
      rw [← hxy, ← hyz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hxz]
  · intro hx
    exact ⟨MulAut.conj c⁻¹ x, ⟨x, hx, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩

theorem card_lt_of_weylHom {H : Type} [Group H] {τ : Tag} {p : ℕ} [Fact p.Prime]
    (hW : GGWeylNoOffender τ p)
    (ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* H) (hι₀ : Function.Injective ι₀)
    {A : Subgroup H} [Finite A] (hA : CFSG.Open.IsElemAbelian p A) (φ : A →* WeylGroup τ)
    (hφ : ∀ (a : A) s, (a : H) * ι₀ (Multiplicative.ofAdd s) * (a : H)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (φ a) s)))
    (hker : ∀ a, φ a = 1 → (a : H) ∈ ι₀.range) (hne : φ.range ≠ ⊥) :
    Nat.card A < p ^ τ.rank := by
  have hφel : CFSG.Open.IsElemAbelian p φ.range := by
    haveI : IsMulCommutative A := hA.1
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_top φ]
      exact Subgroup.map_isMulCommutative _ _
    · intro y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [← map_pow]
      have ha : a ^ p = 1 := Subtype.ext (by simpa using hA.2 (a : H) a.2)
      rw [ha, map_one]
  have hex : ∀ e : φ.ker, ∃ x : {x : Fin τ.rank → ZMod p //
      ∀ a ∈ φ.range, TableBExc.torusAct τ p a x = x},
      ι₀ (Multiplicative.ofAdd x.1) = ((e : A) : H) := by
    intro e
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (hker (e : A) e.2)
    have hu' : ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd u)) = ((e : A) : H) := by
      rwa [ofAdd_toAdd]
    refine ⟨⟨Multiplicative.toAdd u, ?_⟩, hu'⟩
    rintro b ⟨a, rfl⟩
    have hcommA : (e : A) * a = a * (e : A) := hA.1.is_comm.comm (e : A) a
    have hcoe : ((e : A) : H) * (a : H) = (a : H) * ((e : A) : H) := by
      simpa using congrArg (fun z : A => (z : H)) hcommA
    have h2 : (a : H) * ((e : A) : H) * (a : H)⁻¹ = ((e : A) : H) := by
      rw [← hcoe]
      group
    have hφa := hφ a (Multiplicative.toAdd u)
    rw [hu'] at hφa
    have heq : ι₀ (Multiplicative.ofAdd
        (TableBExc.torusAct τ p (φ a) (Multiplicative.toAdd u))) =
        ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd u)) := by
      rw [← hφa, h2, hu']
    exact Multiplicative.ofAdd.injective (hι₀ heq)
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro e₁ e₂ h
    have h' : ι₀ (Multiplicative.ofAdd (g e₁).1) =
        ι₀ (Multiplicative.ofAdd (g e₂).1) := by rw [h]
    rw [hg e₁, hg e₂] at h'
    exact Subtype.ext (Subtype.ext h')
  have hker_le : Nat.card φ.ker ≤ Nat.card {x : Fin τ.rank → ZMod p //
      ∀ a ∈ φ.range, TableBExc.torusAct τ p a x = x} :=
    Nat.card_le_card_of_injective _ hinj
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card {x : Fin τ.rank → ZMod p //
          ∀ a ∈ φ.range, TableBExc.torusAct τ p a x = x} * Nat.card φ.range :=
        Nat.mul_le_mul_right _ hker_le
    _ = Nat.card φ.range * Nat.card {x : Fin τ.rank → ZMod p //
          ∀ a ∈ φ.range, TableBExc.torusAct τ p a x = x} := Nat.mul_comm _ _
    _ < p ^ τ.rank := hW φ.range hφel hne

end ExcFrames

end CFSG.StandardType
