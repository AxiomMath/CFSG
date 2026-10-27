module

public import CFSG.Sporadic.Co2Smith.GlNJG2
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.Sporadic.Co2Smith.GlNJKCompl

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section G

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

structure IsNJComp (L : Subgroup G) : Prop where
  le : L ≤ normalizer (JGc φ : Set G)
  inf : ∀ x ∈ L, x ∈ JGc φ → x = 1
  sup : ∀ n ∈ normalizer (JGc φ : Set G), ∃ j ∈ JGc φ, ∃ l ∈ L, n = j * l

theorem index_NH [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (hφz : φ (zH z) = z0C) :
    ((centralizer ({z} : Set G)).subgroupOf (normalizer (JGc φ : Set G))).index = 77 := by
  let _ : MulAction (normalizer (JGc φ : Set G)) (Fin 77) := MulAction.compHom _ (piG φ hz)
  have hst : MulAction.stabilizer (normalizer (JGc φ : Set G)) (0 : Fin 77) =
      (centralizer ({z} : Set G)).subgroupOf (normalizer (JGc φ : Set G)) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact piG_zero_iff φ hz hφz g
  rw [← hst, MulAction.index_stabilizer]
  have horb : MulAction.orbit (normalizer (JGc φ : Set G)) (0 : Fin 77) = Set.univ := by
    ext k
    simp only [Set.mem_univ, iff_true]
    obtain ⟨n, hn, e⟩ := exists_NG_conj φ hz k
    refine ⟨⟨n, hn⟩, ?_⟩
    show piG φ hz ⟨n, hn⟩ 0 = k
    apply omG_injective φ
    rw [piG_spec, omG_zero φ hφz, e]
  rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] noncomputable def Q0G : Subgroup G := ((QKs 0).subgroupOf Cz).map (phiH φ)

theorem exists_NJComp [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) : ∃ L : Subgroup G, IsNJComp φ L := by
  set NG := normalizer (JGc φ : Set G)
  set V : Subgroup NG := (JGc φ).subgroupOf NG
  have : V.Normal := normal_in_normalizer
  have : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext ((elemTwo_JGc φ).2 _ a.2 _ b.2))⟩⟩
  set P : Subgroup NG := (centralizer ({z} : Set G)).subgroupOf NG
  set K0 : Subgroup NG := (Q0G φ).subgroupOf NG
  have hcop : Nat.Coprime P.index (Nat.card V) := by
    rw [index_NH φ hz hφz, card_subgroupOf_eq le_normalizer, card_JGc]
    norm_num
  have hVK : V ⊓ K0 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxK⟩
    obtain ⟨y, hy, hye⟩ := hxK
    have hye' : phiH φ y = (x : G) := hye
    obtain ⟨w, hw, hwe⟩ := (mem_JGc φ).1 hxV
    have e : w = y := phiH_injective φ (hwe.trans hye'.symm)
    rw [e] at hw
    have h1 := LK_inf_Jc (QKs_zero_le_LK hy) hw
    have h2 : y = 1 := Subtype.ext h1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hye', h2, map_one]
    rfl
  have hsup : V ⊔ K0 = P := by
    apply le_antisymm
    · refine sup_le (fun x hx => JGc_le_H φ hx) ?_
      rintro x ⟨y, -, hy⟩
      have hy' : phiH φ y = (x : G) := hy
      show (x : G) ∈ centralizer ({z} : Set G)
      rw [← hy']
      exact (φ.symm y).2
    · intro x hx
      set y := φ ⟨x, hx⟩
      have hyx : phiH φ y = x := phiH_apply_symm φ x hx
      have hyN : (y : K) ∈ normalizer (Jc : Set K) :=
        (phiH_mem_NG_iff φ y).1 (by rw [hyx]; exact x.2)
      obtain ⟨q, hq, e⟩ := exists_QKs_piK 0 (σ := piK ⟨y, hyN⟩)
        ⟨piK_mem_njAut _, (piK_zero_iff ⟨y, hyN⟩).2 y.2⟩
      have hj : ((y : K) * (q : K)⁻¹) ∈ Jc := by
        have h1 : piK (⟨y, hyN⟩ * q⁻¹) = 1 := by rw [map_mul, map_inv, ← e, mul_inv_cancel]
        exact mem_Jc_of_piK_eq_one h1
      have hqz : (q : K) ∈ Cz := QKs_le_Cz 0 hq
      set jC : Cz := ⟨(y : K) * (q : K)⁻¹, Jc_le_Cz hj⟩
      set qC : Cz := ⟨q, hqz⟩
      have hjq : y = jC * qC := Subtype.ext (by
        show (y : K) = (y : K) * (q : K)⁻¹ * q
        group)
      have hjV : (⟨phiH φ jC, phiH_mem_NG φ (le_normalizer hj)⟩ : NG) ∈ V :=
        (mem_JGc φ).2 ⟨jC, hj, rfl⟩
      have hqK : (⟨phiH φ qC, phiH_mem_NG φ q.2⟩ : NG) ∈ K0 := ⟨qC, hq, rfl⟩
      have hx' : x = ⟨phiH φ jC, phiH_mem_NG φ (le_normalizer hj)⟩ *
          ⟨phiH φ qC, phiH_mem_NG φ q.2⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, ← map_mul, ← hjq, hyx]
      rw [hx']
      exact mul_mem (mem_sup_left hjV) (mem_sup_right hqK)
  obtain ⟨D, -, hVD, hsupD⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V P K0 hcop hVK hsup
  refine ⟨D.map NG.subtype, ⟨?_, ?_, ?_⟩⟩
  · rintro _ ⟨d, -, rfl⟩
    exact d.2
  · rintro _ ⟨d, hd, rfl⟩ hJ
    have hdV : d ∈ V := hJ
    have : d ∈ V ⊓ D := ⟨hdV, hd⟩
    rw [hVD, Subgroup.mem_bot] at this
    rw [this]
    rfl
  · intro n hn
    have hmem : (⟨n, hn⟩ : NG) ∈ V ⊔ D := by rw [hsupD]; exact mem_top _
    obtain ⟨v, hv, d, hd, e⟩ := mem_sup_of_normal_left.1 hmem
    refine ⟨v, hv, d, ⟨d, hd, rfl⟩, ?_⟩
    have e' := congrArg Subtype.val e
    rw [Subgroup.coe_mul] at e'
    exact e'.symm

end G

end CFSG.Sporadic.Co2Smith
