module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def conjK (K : Subgroup G) : ↥(Subgroup.normalizer (K : Set G)) →* MulAut ↥K where
  toFun g :=
    { toFun := fun k => ⟨(g : G) * k * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩
      invFun := fun k => ⟨(g : G)⁻¹ * k * g, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem g.2) k).mp k.2⟩
      left_inv := fun k => by ext; simp [mul_assoc]
      right_inv := fun k => by ext; simp [mul_assoc]
      map_mul' := fun k₁ k₂ => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g₁ g₂ => by ext; simp [mul_assoc]

@[simp] theorem conjK_apply_coe (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G)))
    (k : ↥K) : ((conjK K g k : ↥K) : G) = (g : G) * k * (g : G)⁻¹ := rfl

theorem conj_mem_pCoreK {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {o : G} (ho : o ∈ (CFSG.pCore 2 ↥K).map K.subtype) :
    g * o * g⁻¹ ∈ (CFSG.pCore 2 ↥K).map K.subtype := by
  obtain ⟨o', ho', rfl⟩ := ho
  have hmem : conjK K ⟨g, hg⟩ o' ∈ CFSG.pCore 2 ↥K := by
    rw [← CFSG.pCore_map_iso 2 (conjK K ⟨g, hg⟩)]
    exact Subgroup.mem_map_of_mem _ ho'
  exact ⟨_, hmem, rfl⟩

theorem exists_mem_conj_mem_of_sylowTwoOf [Finite G] {R A B : Subgroup G}
    (hA : QuasithinUnique.IsSylowTwoOf A R) (hBR : B ≤ R) (hBp : IsPGroup 2 B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SA : Sylow 2 R := (hA.2.1.comap_subtype (K := R)).toSylow hA.2.2
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow 2 R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : G) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

theorem le_of_normal_of_sylowTwoOf [Finite G] {R A U : Subgroup G}
    (hA : QuasithinUnique.IsSylowTwoOf A R) (hUR : U ≤ R)
    (hRU : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U) (hU : IsPGroup 2 U) : U ≤ A := by
  obtain ⟨r, hr, hrU⟩ := exists_mem_conj_mem_of_sylowTwoOf hA hUR hU
  intro y hy
  simpa [mul_assoc] using hrU _ (hRU r hr y hy)

theorem isPGroup_zpowers_of_pow_eq_one {a : G} {n : ℕ} (h : a ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)

@[expose] def centQ (T K O : Subgroup G) (hconj : ∀ t ∈ T, ∀ o ∈ O, t * o * t⁻¹ ∈ O)
    (hTK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) : Subgroup G where
  carrier := {t | t ∈ T ∧ ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ O}
  one_mem' := ⟨T.one_mem, fun k _ => by simp⟩
  mul_mem' := fun {t₁ t₂} h₁ h₂ => ⟨T.mul_mem h₁.1 h₂.1, fun k hk => by
    have e : t₁ * t₂ * k * (t₁ * t₂)⁻¹ * k⁻¹ =
        (t₁ * (t₂ * k * t₂⁻¹ * k⁻¹) * t₁⁻¹) * (t₁ * k * t₁⁻¹ * k⁻¹) := by group
    rw [e]
    exact O.mul_mem (hconj t₁ h₁.1 _ (h₂.2 k hk)) (h₁.2 k hk)⟩
  inv_mem' := fun {t} h => ⟨T.inv_mem h.1, fun k hk => by
    have hk' : t⁻¹ * k * t ∈ K := by simpa using hTK t⁻¹ (T.inv_mem h.1) k hk
    have e : t⁻¹ * k * t⁻¹⁻¹ * k⁻¹ = (t * (t⁻¹ * k * t) * t⁻¹ * (t⁻¹ * k * t)⁻¹)⁻¹ := by group
    rw [e]
    exact O.inv_mem (h.2 _ hk')⟩

theorem mem_pCoreOf_of_comm_mem [Finite G] {H K T : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hT : QuasithinUnique.IsSylowTwoOf T H)
    (hKT : K ⊔ T = H) {a : G} (ha : a ∈ H) {n : ℕ} (han : a ^ 2 ^ n = 1)
    (hc : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ (CFSG.pCore 2 ↥K).map K.subtype) :
    a ∈ pCoreOf 2 H := by
  set O := (CFSG.pCore 2 ↥K).map K.subtype with hOdef
  have hOK : O ≤ K := Subgroup.map_subtype_le _
  have hOp : IsPGroup 2 O := CFSG.pCore_isPGroup.map K.subtype
  have hHKe := Subgroup.le_normalizer_iff.mp hHK
  have hOconj : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O := fun h hh o ho => conj_mem_pCoreK (hHK hh) ho
  have hOT : O ≤ T := le_of_normal_of_sylowTwoOf hT (hOK.trans hKH) hOconj hOp
  have hTconj : ∀ t ∈ T, ∀ o ∈ O, t * o * t⁻¹ ∈ O := fun t ht => hOconj t (hT.1 ht)
  have hTK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun t ht => hHKe t (hT.1 ht)
  set Q := centQ T K O hTconj hTK with hQdef
  obtain ⟨r, hr, hrT⟩ := exists_mem_conj_mem_of_sylowTwoOf hT (B := Subgroup.zpowers a)
    (by rw [Subgroup.zpowers_le]; exact ha) (isPGroup_zpowers_of_pow_eq_one han)
  have hbQ : r⁻¹ * a * r ∈ Q := by
    refine ⟨hrT a (Subgroup.mem_zpowers a), fun k hk => ?_⟩
    have e : r⁻¹ * a * r * k * (r⁻¹ * a * r)⁻¹ * k⁻¹ =
        r⁻¹ * (a * (r * k * r⁻¹) * a⁻¹ * (r * k * r⁻¹)⁻¹) * r⁻¹⁻¹ := by group
    rw [e]
    exact hOconj r⁻¹ (H.inv_mem hr) _ (hc _ (hHKe r hr k hk))
  have hQH : Q ≤ H := fun q hq => hT.1 hq.1
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hKT, sup_le_iff, Subgroup.le_normalizer_iff, Subgroup.le_normalizer_iff]
    constructor
    · intro k₀ hk₀ q hq
      refine ⟨?_, fun k hk => ?_⟩
      · have e : k₀ * q * k₀⁻¹ = (q * k₀ * q⁻¹ * k₀⁻¹)⁻¹ * q := by group
        rw [e]
        exact T.mul_mem (hOT (O.inv_mem (hq.2 k₀ hk₀))) hq.1
      · have hk' : k₀⁻¹ * k * k₀ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk₀) hk) hk₀
        have e : k₀ * q * k₀⁻¹ * k * (k₀ * q * k₀⁻¹)⁻¹ * k⁻¹ =
            k₀ * (q * (k₀⁻¹ * k * k₀) * q⁻¹ * (k₀⁻¹ * k * k₀)⁻¹) * k₀⁻¹ := by group
        rw [e]
        exact hOconj k₀ (hKH hk₀) _ (hq.2 _ hk')
    · intro t ht q hq
      refine ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), fun k hk => ?_⟩
      have hk' : t⁻¹ * k * t ∈ K := by simpa using hTK t⁻¹ (T.inv_mem ht) k hk
      have e : t * q * t⁻¹ * k * (t * q * t⁻¹)⁻¹ * k⁻¹ =
          t * (q * (t⁻¹ * k * t) * q⁻¹ * (t⁻¹ * k * t)⁻¹) * t⁻¹ := by group
      rw [e]
      exact hTconj t ht _ (hq.2 _ hk')
  have hQ2 : IsPGroup 2 Q := hT.2.1.to_le (fun q hq => hq.1)
  have hQO : Q ≤ pCoreOf 2 H := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q
    H hQH ((Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHQ) hQ2
  apply hQO
  simpa [mul_assoc] using Subgroup.le_normalizer_iff.mp hHQ r hr _ hbQ

end CFSG.Quasithin.Vol2.Ch11.SecG
