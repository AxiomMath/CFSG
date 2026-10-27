module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.EmptyFaithful.T1515C6Grp
public import CFSG.Quasithin.EmptyFaithful.S152N2Star
public import CFSG.Quasithin.EmptyFaithful.S152UAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

section API

variable {V : Subgroup G}

theorem mem_centralizer_map_iff {Z : Subgroup V} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    x ∈ Subgroup.centralizer ((Z.map V.subtype : Subgroup G) : Set G) ↔
      conjAct V ⟨x, hx⟩ ∈ fixingV (Z : Set V) := by
  constructor
  · intro h z hz
    apply Subtype.ext
    rw [conj_coe_apply]
    have hzG : (z : G) ∈ (Z.map V.subtype : Subgroup G) := ⟨z, hz, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp h z hzG
    calc x * (z : G) * x⁻¹ = (z * x) * x⁻¹ := by rw [h1]
      _ = z := by group
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    obtain ⟨z, hz, rfl⟩ := hg
    have h1 := congrArg (fun w : V => (w : G)) (h z hz)
    simp only [conj_coe_apply] at h1
    show (z : G) * x = x * (z : G)
    calc (z : G) * x = (x * (z : G) * x⁻¹) * x := by rw [h1]
      _ = x * z := by group

theorem inf_centralizer_eq_preOn {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (Z : Subgroup V) :
    M ⊓ Subgroup.centralizer ((Z.map V.subtype : Subgroup G) : Set G) =
      preOn M V (fixingV (Z : Set V)) := by
  ext x
  constructor
  · rintro ⟨hxM, hxc⟩
    exact mem_preOn.mpr ⟨hxM, hMN hxM, (mem_centralizer_map_iff (hMN hxM)).mp hxc⟩
  · intro hx
    obtain ⟨hxM, hxN, hxa⟩ := mem_preOn.mp hx
    exact ⟨hxM, (mem_centralizer_map_iff hxN).mpr hxa⟩

theorem autOn_preOn_inf {M : Subgroup G} (B : Subgroup (MulAut V)) :
    autOn (preOn M V B) V = B ⊓ autOn M V := by
  have h1 : preOn M V B = preOn M V (B ⊓ autOn M V) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxM, hxN, hxB⟩ := mem_preOn.mp hx
      exact mem_preOn.mpr ⟨hxM, hxN, hxB, mem_autOn_of_mem hxN hxM⟩
    · intro hx
      obtain ⟨hxM, hxN, hxB⟩ := mem_preOn.mp hx
      exact mem_preOn.mpr ⟨hxM, hxN, hxB.1⟩
  rw [h1]
  exact autOn_preOn inf_le_right

theorem autOn_map_conj {X : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (V : Set G)) :
    autOn (X.map (MulAut.conj t).toMonoidHom) V =
      (autOn X V).map (MulAut.conj (conjAct V ⟨t, ht⟩)).toMonoidHom :=
  CFSG.Quasithin.AutOn.autOn_map_conj ht

theorem card_eq_card_inf_mul_card_autOn [Finite G] {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card X = Nat.card (X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) *
      Nat.card (autOn X V) := by
  rw [card_autOn_eq_relIndex hX, mul_comm]
  have := Subgroup.relIndex_mul_card (X ⊓ Subgroup.centralizer (V : Set G)) X
  rw [inf_of_le_left (inf_le_left : X ⊓ Subgroup.centralizer (V : Set G) ≤ X)] at this
  exact this.symm

end API


section Setup

variable {V M T : Subgroup G}

theorem isSylowTwoOf_autOn' [Finite G] (hTM : IsSylowTwoOf T M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) : IsSylowTwoOf (autOn T V) (autOn M V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hTM hMN

end Setup


section Ctx

variable {V M T : Subgroup G}

theorem card_autOn_sylow [Finite G] (hTM : IsSylowTwoOf T M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hcardM : Nat.card (autOn M V) = 72) :
    Nat.card (autOn T V) = 8 := by
  have hS := isSylowTwoOf_autOn' hTM hMN
  have hle : autOn T V ≤ autOn M V := autOn_le_autOn V hTM.1
  have h1 : (autOn T V).relIndex (autOn M V) * Nat.card (autOn T V) = Nat.card (autOn M V) := by
    have := Subgroup.relIndex_mul_card (autOn T V) (autOn M V)
    rwa [inf_of_le_left hle] at this
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hodd : ¬ 2 ∣ (autOn T V).relIndex (autOn M V) := hS.2.2
  rw [hcardM, hk] at h1
  generalize (autOn T V).relIndex (autOn M V) = i at h1 hodd
  have hk6 : k < 7 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have hpos : 0 < i := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h1; omega)
    nlinarith
  rw [hk]
  interval_cases k <;> simp_all <;> omega

theorem sixCtx_of_data [Finite G] (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hTsyl : IsSylowTwoOf T M)
    (hcardV : Nat.card V = 256) (hcardM : Nat.card (autOn M V) = 72)
    {A₁ A₂ : Subgroup (MulAut V)} (hA₀M : A₁ ⊔ A₂ ≤ autOn M V)
    (e₁ : Nonempty (A₁ ≃* DihedralGroup 3)) (e₂ : Nonempty (A₂ ≃* DihedralGroup 3))
    (hdisj : A₁ ⊓ A₂ = ⊥) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    {t : G} (ht : t ∈ T)
    (hconj : (preOn M V A₁).map (MulAut.conj t).toMonoidHom = preOn M V A₂)
    (hinf : ⁅V, preOn M V A₁⁆ ⊓ ⁅V, preOn M V A₂⁆ = ⊥)
    (hsup : ⁅V, preOn M V A₁⁆ ⊔ ⁅V, preOn M V A₂⁆ = V) :
    @SixCtx ↥V (commGroupOfElemAbelian hVe) A₁ A₂ (autOn M V) (autOn T V)
      (conjAct V ⟨t, hMN (hTsyl.1 ht)⟩) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hA₁M : A₁ ≤ autOn M V := le_sup_left.trans hA₀M
  have hA₂M : A₂ ≤ autOn M V := le_sup_right.trans hA₀M
  have hM₁N : preOn M V A₁ ≤ Subgroup.normalizer (V : Set G) := (preOn_le M V A₁).trans hMN
  have hM₂N : preOn M V A₂ ≤ Subgroup.normalizer (V : Set G) := (preOn_le M V A₂).trans hMN
  have hV₁ : ⁅V, preOn M V A₁⁆ = (commV A₁).map V.subtype := by
    rw [S152N2.commutator_eq_map_commV hVe hM₁N, autOn_preOn hA₁M]
  have hV₂ : ⁅V, preOn M V A₂⁆ = (commV A₂).map V.subtype := by
    rw [S152N2.commutator_eq_map_commV hVe hM₂N, autOn_preOn hA₂M]
  have hinj : Function.Injective V.subtype := V.subtype_injective
  refine
    { sq := fun v => ?_
      card_V := hcardV
      e₁ := e₁
      e₂ := e₂
      comm := hcomm
      disj := hdisj
      le_M := hA₀M
      card_M := hcardM
      le_T := autOn_le_autOn V hTsyl.1
      card_T := card_autOn_sylow hTsyl hMN hcardM
      tau_mem := mem_autOn_of_mem (hMN (hTsyl.1 ht)) ht
      tau_conj := ?_
      dsum_inf := ?_
      dsum_sup := ?_ }
  · apply Subtype.ext
    show (v : G) * v = 1
    rw [← pow_two]
    exact hVe.2 _ v.2
  · have h1 := autOn_map_conj (X := preOn M V A₁) (V := V) (hMN (hTsyl.1 ht))
    rw [hconj, autOn_preOn hA₂M, autOn_preOn hA₁M] at h1
    exact h1.symm
  · rw [hV₁, hV₂, ← Subgroup.map_inf _ _ _ hinj] at hinf
    exact (Subgroup.map_eq_bot_iff_of_injective (commV A₁ ⊓ commV A₂) hinj).mp hinf
  · rw [hV₁, hV₂, ← Subgroup.map_sup] at hsup
    have : (commV A₁ ⊔ commV A₂).map V.subtype = (⊤ : Subgroup V).map V.subtype := by
      rw [hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective hinj this

end Ctx

end CFSG.Quasithin
