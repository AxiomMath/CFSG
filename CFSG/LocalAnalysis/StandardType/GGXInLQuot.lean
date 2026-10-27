module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

public section

open scoped Pointwise

namespace CFSG.StandardType.GGXInL

private lemma lup8c_card_inf_eq_bot {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (E N : Subgroup H) (hNp : Nat.Coprime p (Nat.card N)) (hEp : IsPGroup p E) :
    E ⊓ N = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hpg : IsPGroup p ↥(E ⊓ N) := hEp.to_inf_left (K := N)
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hpg
  have hdiv : Nat.card ↥(E ⊓ N) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (p ^ n) (Nat.card N) := hNp.pow_left n
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hn hdiv)

private lemma lup8c_card_sup {H : Type*} [Group H] (E N : Subgroup H) [N.Normal]
    (hbot : E ⊓ N = ⊥) :
    Nat.card ↥(E ⊔ N) = Nat.card ↥E * Nat.card ↥N := by
  have h1 : N.relIndex (E ⊔ N) * Nat.card ↥(N ⊓ (E ⊔ N)) = Nat.card ↥(E ⊔ N) :=
    Subgroup.relIndex_mul_card N (E ⊔ N)
  have h2 : N ⊓ (E ⊔ N) = N := inf_of_le_left le_sup_right
  have h3 : N.relIndex (E ⊔ N) = N.relIndex E := Subgroup.relIndex_sup_right E N
  have h4 : N.relIndex E * Nat.card ↥(N ⊓ E) = Nat.card ↥E := Subgroup.relIndex_mul_card N E
  have h5 : N ⊓ E = ⊥ := by rw [inf_comm]; exact hbot
  have h6 : Nat.card ↥(N ⊓ E) = 1 := by rw [h5]; simp
  have h7 : N.relIndex E = Nat.card ↥E := by
    rw [h6, mul_one] at h4; exact h4
  calc Nat.card ↥(E ⊔ N) = N.relIndex (E ⊔ N) * Nat.card ↥(N ⊓ (E ⊔ N)) := h1.symm
    _ = Nat.card ↥E * Nat.card ↥N := by rw [h3, h7, h2]

private lemma lup8c_relIndex_eq {H : Type*} [Group H] [Finite H] (E N K : Subgroup H)
    (hcard : Nat.card ↥(E ⊔ N) = Nat.card ↥E * Nat.card ↥N)
    (hKG : K ≤ E ⊔ N) (hcardK : Nat.card ↥K = Nat.card ↥E) :
    K.relIndex (E ⊔ N) = Nat.card ↥N := by
  have : Finite ↥E := Finite.of_injective (Subtype.val : ↥E → H) Subtype.val_injective
  have h1 : K.relIndex (E ⊔ N) * Nat.card ↥(K ⊓ (E ⊔ N)) = Nat.card ↥(E ⊔ N) :=
    Subgroup.relIndex_mul_card K (E ⊔ N)
  have h2 : K ⊓ (E ⊔ N) = K := inf_of_le_left hKG
  rw [h2, hcardK, hcard] at h1
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥E)) (by rw [h1, mul_comm (Nat.card ↥N)])

private lemma lup8c_map_conj_subtype {G : Type*} [Group G] {K : Subgroup G} (g : K) (A : Subgroup G)
    (hA : A ≤ K) :
    Subgroup.map K.subtype (Subgroup.map (MulAut.conj g) (A.subgroupOf K)) =
      Subgroup.map (MulAut.conj (g : G)) A := by
  rw [Subgroup.map_map]
  have hcomp : K.subtype.comp (MulAut.conj g) =
      ((MulAut.conj (g : G) : G →* G)).comp K.subtype := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hA]

private lemma lup8c_sylow_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) :
    ∃ g : G, Subgroup.map (MulAut.conj g) (P : Subgroup G) = (Q : Subgroup G) := by
  have : Finite (Sylow p G) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) P Q
  refine ⟨g, ?_⟩
  have hsmul : ((g • P : Sylow p G) : Subgroup G) = MulAut.conj g • (P : Subgroup G) :=
    Subgroup.ext (fun x => by rw [Sylow.coe_subgroup_smul])
  have hmap : MulAut.conj g • (P : Subgroup G) = Subgroup.map (MulAut.conj g) (P : Subgroup G) := by
    rw [Subgroup.pointwise_smul_def]
    congr 1
  exact hmap.symm.trans (hsmul.symm.trans (congrArg (fun S : Sylow p G => (S : Subgroup G)) hg))

private lemma lup8c_mulAut_coe_mul {H : Type*} [Group H] (e₁ e₂ : MulAut H) :
    (↑(e₁ * e₂) : H →* H) = (↑e₁ : H →* H).comp (↑e₂ : H →* H) := by
  ext x; rfl

private lemma lup8c_mulAut_coe_one {H : Type*} [Group H] :
    (↑(1 : MulAut H) : H →* H) = MonoidHom.id H := by
  ext x; rfl

lemma lup8c_mem_map_inf_normalizer {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (L E N : Subgroup H) [N.Normal] (hNL : N ≤ L)
    (hNp : Nat.Coprime p (Nat.card N)) (hEp : IsPGroup p E) {n : H} (hnL : n ∈ L)
    (hn : (QuotientGroup.mk' N) n ∈
      Subgroup.normalizer ((E.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))) :
    (QuotientGroup.mk' N) n ∈ (L ⊓ Subgroup.normalizer (E : Set H)).map (QuotientGroup.mk' N) := by
  have hbot : E ⊓ N = ⊥ := lup8c_card_inf_eq_bot E N hNp hEp
  have hcard : Nat.card ↥(E ⊔ N) = Nat.card ↥E * Nat.card ↥N := lup8c_card_sup E N hbot
  have hEG' : E ≤ E ⊔ N := le_sup_left
  have hFG' : E.map (MulAut.conj n : H →* H) ≤ E ⊔ N := by
    have hle : E.map (MulAut.conj n : H →* H) ≤
        Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) E) := by
      rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_comap]
      have hpe : (QuotientGroup.mk' N) e ∈ Subgroup.map (QuotientGroup.mk' N) E :=
        Subgroup.mem_map_of_mem (QuotientGroup.mk' N) he
      have hmem : (QuotientGroup.mk' N) n * (QuotientGroup.mk' N) e *
          ((QuotientGroup.mk' N) n)⁻¹ ∈ Subgroup.map (QuotientGroup.mk' N) E :=
        (Subgroup.mem_normalizer_iff.mp hn ((QuotientGroup.mk' N) e)).mp hpe
      simpa [map_mul] using hmem
    have hcomap : Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) E) =
        E ⊔ N := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rwa [hcomap] at hle
  have hcardF : Nat.card ↥(E.map (MulAut.conj n : H →* H)) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (f := (MulAut.conj n : H →* H)) (MulAut.conj n).injective
  have hpN : ¬ p ∣ Nat.card ↥N := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hNp
  have hrelE : (E.subgroupOf (E ⊔ N)).index = Nat.card ↥N :=
    lup8c_relIndex_eq E N E hcard hEG' rfl
  have hrelF : ((E.map (MulAut.conj n : H →* H)).subgroupOf (E ⊔ N)).index = Nat.card ↥N :=
    lup8c_relIndex_eq E N (E.map (MulAut.conj n : H →* H)) hcard hFG' hcardF
  let P : Sylow p ↥(E ⊔ N) :=
    (hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEG').symm).toSylow (by rw [hrelE]; exact hpN)
  let Q : Sylow p ↥(E ⊔ N) :=
    ((hEp.map (MulAut.conj n : H →* H)).of_equiv (Subgroup.subgroupOfEquivOfLe hFG').symm).toSylow
      (by rw [hrelF]; exact hpN)
  have hPsub : (P : Subgroup ↥(E ⊔ N)) = E.subgroupOf (E ⊔ N) := rfl
  have hQsub : (Q : Subgroup ↥(E ⊔ N)) = (E.map (MulAut.conj n : H →* H)).subgroupOf (E ⊔ N) := rfl
  have hPcoe : Subgroup.map (E ⊔ N).subtype (P : Subgroup ↥(E ⊔ N)) = E := by
    rw [hPsub]; exact Subgroup.map_subgroupOf_eq_of_le hEG'
  have hQcoe : Subgroup.map (E ⊔ N).subtype (Q : Subgroup ↥(E ⊔ N)) =
      E.map (MulAut.conj n : H →* H) := by
    rw [hQsub]; exact Subgroup.map_subgroupOf_eq_of_le hFG'
  obtain ⟨g, hg⟩ := lup8c_sylow_conj P Q
  have hconjE : E.map (MulAut.conj (g : H) : H →* H) = E.map (MulAut.conj n : H →* H) := by
    have h1 := lup8c_map_conj_subtype (G := H) (K := E ⊔ N) g E hEG'
    have h2 : Subgroup.map (MulAut.conj g) (E.subgroupOf (E ⊔ N)) =
        (Q : Subgroup ↥(E ⊔ N)) := by rw [← hPsub]; exact hg
    rw [h2, hQcoe] at h1
    exact h1.symm
  have hmem : (g : H) ∈ (N : Set H) * (E : Set H) := by
    rw [← Subgroup.normal_mul N E, sup_comm]
    exact g.2
  obtain ⟨a, haN, e, heE, hae⟩ := Set.mem_mul.mp hmem
  have hEe : E.map (MulAut.conj e : H →* H) = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer heE)
  have hconj : MulAut.conj (g : H) = MulAut.conj a * MulAut.conj e := by
    rw [← hae, map_mul]
  have hEga : E.map (MulAut.conj (g : H) : H →* H) = E.map (MulAut.conj a : H →* H) := by
    rw [hconj, lup8c_mulAut_coe_mul, ← Subgroup.map_map, hEe]
  have hEan : E.map (MulAut.conj a : H →* H) = E.map (MulAut.conj n : H →* H) :=
    hEga.symm.trans hconjE
  have hnorm : a⁻¹ * n ∈ Subgroup.normalizer (E : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h2 : MulAut.conj (a⁻¹ * n) = MulAut.conj a⁻¹ * MulAut.conj n :=
      map_mul (MulAut.conj) a⁻¹ n
    have h3 : E.map (MulAut.conj (a⁻¹ * n) : H →* H) =
        Subgroup.map (MulAut.conj a⁻¹ : H →* H) (E.map (MulAut.conj n : H →* H)) := by
      rw [h2, lup8c_mulAut_coe_mul, ← Subgroup.map_map]
    have h4 : Subgroup.map (MulAut.conj a⁻¹ : H →* H)
        (E.map (MulAut.conj n : H →* H)) = E := by
      rw [← hEan]
      rw [Subgroup.map_map]
      rw [← lup8c_mulAut_coe_mul]
      rw [← map_mul]
      rw [inv_mul_cancel]
      rw [map_one]
      rw [lup8c_mulAut_coe_one]
      rw [Subgroup.map_id]
    rw [h3, h4]
  have hpa : (QuotientGroup.mk' N) a = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact haN
  have hpi : (QuotientGroup.mk' N) (a⁻¹ * n) = (QuotientGroup.mk' N) n := by
    rw [map_mul, map_inv, hpa, inv_one, one_mul]
  have hmem2 : (QuotientGroup.mk' N) (a⁻¹ * n) ∈
      (L ⊓ Subgroup.normalizer (E : Set H)).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ ⟨mul_mem (hNL (inv_mem haN)) hnL, hnorm⟩
  rwa [hpi] at hmem2

private lemma lup8c_map_inf_normalizer {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (L E N : Subgroup H) [N.Normal] (hNL : N ≤ L)
    (hNp : Nat.Coprime p (Nat.card N)) (hEp : IsPGroup p E) :
    (L ⊓ Subgroup.normalizer (E : Set H)).map (QuotientGroup.mk' N) =
      L.map (QuotientGroup.mk' N) ⊓
        Subgroup.normalizer ((E.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact ((Subgroup.map_inf_le L (Subgroup.normalizer (E : Set H))
        (QuotientGroup.mk' N))).trans inf_le_left
    · exact (((Subgroup.map_inf_le L (Subgroup.normalizer (E : Set H))
        (QuotientGroup.mk' N))).trans inf_le_right).trans
        (Subgroup.le_normalizer_map (QuotientGroup.mk' N))
  · rintro y ⟨hyL, hyn⟩
    obtain ⟨n, hnL, rfl⟩ := Subgroup.mem_map.mp hyL
    exact lup8c_mem_map_inf_normalizer L E N hNL hNp hEp hnL hyn

theorem mem_commutator_iff_map_quotient
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (L E N : Subgroup H) [N.Normal]
    (hNL : N ≤ L) (hNp : Nat.Coprime p (Nat.card N)) (hEp : IsPGroup p E) {x : H} (hx : x ∈ E) :
    x ∈ ⁅E, L ⊓ Subgroup.normalizer (E : Set H)⁆ ↔
      (x : H ⧸ N) ∈ ⁅E.map (QuotientGroup.mk' N), L.map (QuotientGroup.mk' N) ⊓
        Subgroup.normalizer ((E.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))⁆ := by
  have hmap := lup8c_map_inf_normalizer L E N hNL hNp hEp
  constructor
  · intro hxK
    have hmem : (QuotientGroup.mk' N) x ∈
        Subgroup.map (QuotientGroup.mk' N) ⁅E, L ⊓ Subgroup.normalizer (E : Set H)⁆ :=
      Subgroup.mem_map_of_mem _ hxK
    rwa [Subgroup.map_commutator, hmap] at hmem
  · intro hxq
    have hxq' : (QuotientGroup.mk' N) x ∈
        Subgroup.map (QuotientGroup.mk' N) ⁅E, L ⊓ Subgroup.normalizer (E : Set H)⁆ := by
      rwa [Subgroup.map_commutator, hmap]
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxq'
    have hcE : c ∈ E := by
      have hle : ⁅E, L ⊓ Subgroup.normalizer (E : Set H)⁆ ≤ E := by
        rw [Subgroup.commutator_le]
        intro e he k hk
        rw [commutatorElement_def]
        have hkE : k * e⁻¹ * k⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.mp hk.2 e⁻¹).mp (inv_mem he)
        simpa [mul_assoc] using mul_mem he hkE
      exact hle hc
    have hcx' : c = x := by
      have hker : c⁻¹ * x ∈ (QuotientGroup.mk' N).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
      rw [QuotientGroup.ker_mk'] at hker
      have hmem : c⁻¹ * x ∈ E ⊓ N := Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hcE) hx, hker⟩
      rw [lup8c_card_inf_eq_bot E N hNp hEp] at hmem
      exact inv_mul_eq_one.mp (by simpa using hmem)
    rw [← hcx']
    exact hc


end CFSG.StandardType.GGXInL

end
