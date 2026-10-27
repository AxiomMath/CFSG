module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211B
public import CFSG.Quasithin.Vol2.Ch8Sec2L8211C
public import CFSG.Quasithin.Vol2.Ch8Sec2L8211D
public import CFSG.Quasithin.Vol2.Ch8Sec2HZ

public section

namespace CFSG.Quasithin.H13.L8211

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu

theorem sq_eq_one_of_equiv {n : ℕ} {V : Type} [CommGroup V] (e : V ≃* Wn n) (v : V) :
    v ^ 2 = 1 := by
  obtain ⟨m, -, hm⟩ := toW_surj n (e v)
  apply e.injective
  rw [map_pow, ← hm, map_one, pow_two, ← toW_xor, Nat.xor_self, toW_zero]

theorem mem_normalizer_inf {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hA x) (Subgroup.mem_normalizer_iff.mp hB x)

theorem mem_normalizer_parz82 {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {z : V}
    {q : MulAut V} (hqN : q ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hqz : q ∈ centSub (Subgroup.zpowers z)) :
    q ∈ Subgroup.normalizer (parz82 H z : Set (MulAut V)) :=
  normalizer_le_normalizer_perfectCore _
    (mem_normalizer_inf hqN (mem_normalizer_centSub (centSub_le_stabSub _ hqz)))

theorem hyp_of_model
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {e : ℕ} (hmod : IsModel82e H e) {z : V} (hz1 : z ≠ 1)
    (hSyl : IsSylowVec82 H z) (hsq : ∀ v : V, v ^ 2 = 1) : Hyp (parz82 H z) z e := by
  obtain ⟨hW, hR, -, hmin, hirr, hfix, hcomm⟩ := hZ82_holds V H e z hmod hz1 hSyl
  exact ⟨hsq, hz1, (perfectCore_le _).trans inf_le_right, hW, hR, hmin, hirr, hfix, hcomm⟩

theorem pCoreOf_parz82_sup
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {e : ℕ} (hmod : IsModel82e H e) {z : V} (hz1 : z ≠ 1)
    (hSyl : IsSylowVec82 H z) {S : Subgroup (MulAut V)}
    (hSN : S ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hSz : S ≤ centSub (Subgroup.zpowers z)) :
    pCoreOf 2 (parz82 H z ⊔ S) = radz82 H z := by
  have : Finite (MulAut V) := finite_mulAut
  obtain ⟨S₀, hS₀H, hS₀c, hzS₀⟩ := hSyl
  have hSyl' : IsSylowVec82 H z := ⟨S₀, hS₀H, hS₀c, hzS₀⟩
  have hPN : parz82 H z ≤ Subgroup.normalizer (H : Set (MulAut V)) := fun p hp =>
    Subgroup.le_normalizer ((perfectCore_le _ hp).1)
  have hPz : parz82 H z ≤ centSub (Subgroup.zpowers z) := (perfectCore_le _).trans inf_le_right
  have key : ∀ q ∈ Subgroup.normalizer (H : Set (MulAut V)), q ∈ centSub (Subgroup.zpowers z) →
      (∃ k : ℕ, q ^ 2 ^ k = 1) → (∀ p ∈ parz82 H z, q * p * q⁻¹ * p⁻¹ ∈ radz82 H z) →
      q ∈ radz82 H z := by
    intro q hqN hqz hq2 hqP
    have hqNP := mem_normalizer_parz82 hqN hqz
    have hqz' : q z = z := hqz z (Subgroup.mem_zpowers z)
    rcases hmod with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · obtain ⟨e, -, -⟩ := CFSG.Quasithin.H.L34Z.exists_equiv_z0 h hz1 hS₀H hS₀c hzS₀
      have hyp := hyp_of_model (Or.inl ⟨h, rfl⟩) hz1 hSyl' (sq_eq_one_of_equiv e)
      exact hyp.mem_rad (CFSG.Quasithin.H.L34Z.irrV_of_binaryNine h hz1 hS₀H hS₀c hzS₀) hqNP hq2
        hqP hqz'
    · obtain ⟨e, -, -⟩ := CFSG.Quasithin.H.Code22.exists_equiv_z0 h hz1 hS₀H hS₀c hzS₀
      have hyp := hyp_of_model (Or.inr (Or.inl ⟨h, rfl⟩)) hz1 hSyl' (sq_eq_one_of_equiv e)
      refine hyp.mem_rad_of hqNP hq2 hqP hqz' fun q' hq' _ hcomm => ?_
      have hle : radz82 H z ⊔ Subgroup.zpowers q ≤ Subgroup.normalizer (H : Set (MulAut V)) :=
        sup_le (fun r hr => hPN (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr))
          (Subgroup.zpowers_le.mpr hqN)
      exact CFSG.Quasithin.H.Code22.faith_of_code22 h hz1 hS₀H hS₀c hzS₀ q' (hle hq') hcomm
    · obtain ⟨e, -, -⟩ := CFSG.Quasithin.H.Coc24.exists_equiv_z0 h hz1 hS₀H hS₀c hzS₀
      have hyp := hyp_of_model (Or.inr (Or.inr ⟨h, rfl⟩)) hz1 hSyl' (sq_eq_one_of_equiv e)
      exact hyp.mem_rad (CFSG.Quasithin.H.Coc24.irrV_of_cocode24 h hz1 hS₀H hS₀c hzS₀) hqNP hq2
        hqP hqz'
  have hSP : S ≤ Subgroup.normalizer (parz82 H z : Set (MulAut V)) := fun s hs =>
    mem_normalizer_parz82 (hSN hs) (hSz hs)
  have hPSP : parz82 H z ⊔ S ≤ Subgroup.normalizer (parz82 H z : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hSP
  refine le_antisymm (fun q hq => ?_) ?_
  · have hqPS : q ∈ parz82 H z ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    have hqN : q ∈ Subgroup.normalizer (H : Set (MulAut V)) := sup_le hPN hSN hqPS
    have hqz : q ∈ centSub (Subgroup.zpowers z) := sup_le hPz hSz hqPS
    have hQ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (parz82 H z ⊔ S)
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    have hq2 : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine key q hqN hqz ⟨k, hq2⟩ fun p hp => ?_
    have hpPS : p ∈ parz82 H z ⊔ S := Subgroup.mem_sup_left hp
    have h1 : q * p * q⁻¹ * p⁻¹ ∈ pCoreOf 2 (parz82 H z ⊔ S) := by
      have h2 : p * q⁻¹ * p⁻¹ ∈ pCoreOf 2 (parz82 H z ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hpPS) _).mp (Subgroup.inv_mem _ hq)
      have e1 : q * p * q⁻¹ * p⁻¹ = q * (p * q⁻¹ * p⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hq h2
    have h3 : q * p * q⁻¹ * p⁻¹ ∈ parz82 H z := by
      have h4 : q * p * q⁻¹ ∈ parz82 H z :=
        (Subgroup.mem_normalizer_iff.mp (hPSP hqPS) p).mp hp
      exact Subgroup.mul_mem _ h4 (Subgroup.inv_mem _ hp)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_ ⟨h1, h3⟩
    · intro p' hp'
      exact mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (Subgroup.mem_sup_left hp')) (Subgroup.le_normalizer hp')
    · exact hQ2.to_le inf_le_left
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact fun x hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hPSP hx)

end CFSG.Quasithin.H13.L8211
