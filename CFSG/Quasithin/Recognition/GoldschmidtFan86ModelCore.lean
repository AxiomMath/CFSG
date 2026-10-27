module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Basic

theorem pCoreOf_top_eq (G : Type*) [Group G] : pCoreOf 2 (⊤ : Subgroup G) = Open.pCore 2 G := by
  unfold pCoreOf
  rw [← map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := G)).symm, Subgroup.map_map]
  have h : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x
    rfl
  rw [h, Subgroup.map_id]

variable {G : Type*} [Group G]

theorem card_pCoreOf (L : Subgroup G) : Nat.card (pCoreOf 2 L) = Nat.card (Open.pCore 2 ↥L) :=
  Subgroup.card_map_of_injective L.subtype_injective

theorem mem_pCoreOf_iff (L : Subgroup G) (x : ↥L) :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ Open.pCore 2 ↥L := by
  unfold pCoreOf
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem charTwo_top_of_charTwo (L : Subgroup G) (h : CharTwo L) : CharTwo (⊤ : Subgroup ↥L) := by
  intro x hx
  rw [pCoreOf_top_eq]
  have hxc : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    intro y hy
    have hy' : (⟨y, pCoreOf_le 2 L hy⟩ : ↥L) ∈ Open.pCore 2 ↥L :=
      (mem_pCoreOf_iff L ⟨y, pCoreOf_le 2 L hy⟩).1 hy
    have hxc' := hx.2
    rw [pCoreOf_top_eq] at hxc'
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxc' _ hy')
  exact (mem_pCoreOf_iff L x).1 (h ⟨x.2, hxc⟩)

theorem conj_mem_centralizer {Q : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    {x : G} (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * q * g)).2
    have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
    rw [e] at h
    exact h hq
  have h1 := Subgroup.mem_centralizer_iff.1 hx _ hq'
  calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
    _ = (g * x * g⁻¹) * q := by group

end Basic

section CharTwo

variable {N : Type*} [Group N] [Finite N]

theorem charTwo_of_index_le_two {X X' J : Subgroup N} (hXX' : X ≤ X')
    (hidx : X.relIndex X' ≤ 2) (hJ : IsPGroup 2 J) (hJX : J ≤ X)
    (hn : X' ≤ Subgroup.normalizer (J : Set N))
    (hC : X ⊓ Subgroup.centralizer (J : Set N) ≤ J) : CharTwo X' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJQ : J ≤ pCoreOf 2 X' := le_pCoreOf_of_le_normalizer 2 (hJX.trans hXX') hn hJ
  set C := X' ⊓ Subgroup.centralizer (pCoreOf 2 X' : Set N) with hCdef
  have hXC : X ⊓ C ≤ J := fun x hx =>
    hC ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hJQ) hx.2.2⟩
  have hXCp : IsPGroup 2 ↥(X ⊓ C) := hJ.to_le hXC
  obtain ⟨k, hk⟩ := hXCp.exists_card_eq
  have hCle : C ≤ X' := inf_le_left
  have hr : X.relIndex C ≤ 2 := by
    refine (Subgroup.relIndex_le_of_le_right hCle ?_).trans hidx
    exact Subgroup.index_ne_zero_of_finite
  have hr0 : X.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard := Subgroup.relIndex_mul_card (H := X) (K := C)
  rw [hk] at hcard
  have hCp : IsPGroup 2 ↥C := by
    have h12 : X.relIndex C = 1 ∨ X.relIndex C = 2 := by omega
    rcases h12 with h | h
    · exact IsPGroup.of_card (n := k) (by rw [← hcard, h, one_mul])
    · exact IsPGroup.of_card (n := k + 1) (by rw [← hcard, h, pow_succ, mul_comm])
  have hCn : X' ≤ Subgroup.normalizer (C : Set N) := by
    intro g hg
    have hgQ := le_normalizer_pCoreOf 2 X' hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨X'.mul_mem (X'.mul_mem hg hx1) (X'.inv_mem hg), conj_mem_centralizer hgQ hx2⟩
    · rintro ⟨hx1, hx2⟩
      have hg' : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 X' : Set N) := Subgroup.inv_mem _ hgQ
      refine ⟨?_, ?_⟩
      · have := X'.mul_mem (X'.mul_mem (X'.inv_mem hg) hx1) hg
        simpa [mul_assoc] using this
      · have := conj_mem_centralizer hg' hx2
        simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer 2 hCle hCn hCp

end CharTwo

section Quotient

variable (G : Type*) [Group G] [Finite G]

theorem pCore_quotient_pCore_eq_bot : Open.pCore 2 (G ⧸ Open.pCore 2 G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := Open.pCore 2 G
  have : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π : G →* G ⧸ Q := QuotientGroup.mk' Q with hπ
  set R : Subgroup (G ⧸ Q) := Open.pCore 2 (G ⧸ Q) with hR
  have hRn : R.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hR'n : (R.comap π).Normal := hRn.comap π
  have hR'p : IsPGroup 2 ↥(R.comap π) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := G ⧸ Q) 2) ⟨π x, hx⟩
    have hxm : π (x ^ 2 ^ m) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hm
    have hxQ : x ^ 2 ^ m ∈ Q := (QuotientGroup.eq_one_iff _).1 hxm
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := G) 2) ⟨x ^ 2 ^ m, hxQ⟩
    refine ⟨m + n, Subtype.ext ?_⟩
    have hn' : (x ^ 2 ^ m) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    change x ^ 2 ^ (m + n) = 1
    rw [pow_add, pow_mul]
    exact hn'
  have hle : R.comap π ≤ Q := CFSG.LieType.BorelTits.le_pCore 2 hR'n hR'p
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ Q := hle hy
  exact (QuotientGroup.eq_one_iff x).2 hx

omit [Finite G] in
theorem card_oTwoQuot_mul : Nat.card (oTwoQuot G) * Nat.card (Open.pCore 2 G) = Nat.card G :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 G)).symm

end Quotient

end CFSG.Quasithin.Fan86.Model
