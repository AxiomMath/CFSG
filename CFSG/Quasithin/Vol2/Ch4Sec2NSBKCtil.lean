module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinF
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem le_pCoreOf_of_commutes_mod {G : Type} [Group G] [Finite G] {K R : Subgroup G} {n : ℕ}
    (hR2 : IsPGroup 2 ↥R) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (α : ↥K →* GL (Fin n) (ZMod 2)) (hsurj : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K)
    (y : G) (hy : y ∈ K ⊔ R) (hcomm : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    y ∈ pCoreOf 2 (K ⊔ R) := by
  set X : Subgroup G := K ⊔ R
  set O : Subgroup G := pCoreOf 2 K
  have hOeq : O = (CFSG.pCore 2 ↥K).map K.subtype :=
    CFSG.Quasithin.C2A3Orbits.pCoreOf_eq_map_pCore K
  have hmemO : ∀ x : ↥K, (x : G) ∈ O ↔ x ∈ CFSG.pCore 2 ↥K := fun x => by
    rw [hOeq]
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hnO : ∀ z ∈ X, ∀ o ∈ O, z * o * z⁻¹ ∈ O := fun z hz o ho =>
    (Subgroup.mem_normalizer_iff.mp (hXO hz) o).mp ho
  have hnK : ∀ z ∈ X, ∀ k ∈ K, z⁻¹ * k * z ∈ K := by
    intro z hz k hk
    refine (Subgroup.mem_normalizer_iff.mp (hXN hz) (z⁻¹ * k * z)).mpr ?_
    have e : z * (z⁻¹ * k * z) * z⁻¹ = k := by group
    rw [e]
    exact hk
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G,
      ∀ z, z ∈ C ↔ (z ∈ X ∧ ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ O) := by
    refine ⟨{ carrier := {z | z ∈ X ∧ ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ O}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun z => Iff.rfl⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      show a * b ∈ X ∧ ∀ k ∈ K, a * b * k * (a * b)⁻¹ * k⁻¹ ∈ O
      refine ⟨X.mul_mem ha hb, fun k hk => ?_⟩
      have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
          (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
      rw [e]
      exact O.mul_mem (hnO a ha _ (hb' k hk)) (ha' k hk)
    · show (1 : G) ∈ X ∧ ∀ k ∈ K, (1 : G) * k * (1 : G)⁻¹ * k⁻¹ ∈ O
      refine ⟨X.one_mem, fun k _ => ?_⟩
      simpa using O.one_mem
    · rintro a ⟨ha, ha'⟩
      show a⁻¹ ∈ X ∧ ∀ k ∈ K, a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ ∈ O
      refine ⟨X.inv_mem ha, fun k hk => ?_⟩
      have e : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = (a * (a⁻¹ * k * a) * a⁻¹ * (a⁻¹ * k * a)⁻¹)⁻¹ := by
        group
      rw [e]
      exact O.inv_mem (ha' _ (hnK a ha k hk))
  have hCX : C ≤ X := fun z hz => ((hC z).mp hz).1
  have hCcond : ∀ z ∈ C, ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ O := fun z hz => ((hC z).mp hz).2
  have hkey : ∀ a ∈ X, ∀ z ∈ C, a * z * a⁻¹ ∈ C := by
    intro a ha z hz
    rw [hC]
    refine ⟨X.mul_mem (X.mul_mem ha (hCX hz)) (X.inv_mem ha), fun k hk => ?_⟩
    have e : a * z * a⁻¹ * k * (a * z * a⁻¹)⁻¹ * k⁻¹ =
        a * (z * (a⁻¹ * k * a) * z⁻¹ * (a⁻¹ * k * a)⁻¹) * a⁻¹ := by group
    rw [e]
    exact hnO a ha _ (hCcond z hz _ (hnK a ha k hk))
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hkey a ha z hz
    · intro hz
      have h := hkey a⁻¹ (X.inv_mem ha) _ hz
      have e : a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ = z := by group
      rw [e] at h
      exact h
  have hCp : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨e, he⟩ := CFSG.Quasithin.InternalSec.two_of_sup hR2 hRK (c : G) (hCX c.2)
    set w : G := (c : G) ^ 2 ^ e
    have hwC : w ∈ C := C.pow_mem c.2 _
    have hwK : w ∈ K := he
    have hcomm' : ∀ k : ↥K, α ⟨w, hwK⟩ * α k = α k * α ⟨w, hwK⟩ := by
      intro k
      have hcoe : (((⟨w, hwK⟩ : ↥K) * k * (⟨w, hwK⟩ : ↥K)⁻¹ * k⁻¹ : ↥K) : G) =
          w * (k : G) * w⁻¹ * (k : G)⁻¹ := rfl
      have hxO : (((⟨w, hwK⟩ : ↥K) * k * (⟨w, hwK⟩ : ↥K)⁻¹ * k⁻¹ : ↥K) : G) ∈ O := by
        rw [hcoe]
        exact hCcond w hwC (k : G) k.2
      have hmem : (⟨w, hwK⟩ : ↥K) * k * (⟨w, hwK⟩ : ↥K)⁻¹ * k⁻¹ ∈ α.ker := by
        rw [hker]
        exact (hmemO _).mp hxO
      simp only [MonoidHom.mem_ker, map_mul, map_inv] at hmem
      calc α ⟨w, hwK⟩ * α k
          = (α ⟨w, hwK⟩ * α k * (α ⟨w, hwK⟩)⁻¹ * (α k)⁻¹) * (α k * α ⟨w, hwK⟩) := by group
        _ = α k * α ⟨w, hwK⟩ := by rw [hmem, one_mul]
    have hcentral : ∀ x : GL (Fin n) (ZMod 2), α ⟨w, hwK⟩ * x = x * α ⟨w, hwK⟩ := by
      intro x
      obtain ⟨k, rfl⟩ := hsurj x
      exact hcomm' k
    have hαw : α ⟨w, hwK⟩ = 1 := gl_zmod_two_central _ hcentral
    have hwpc : (⟨w, hwK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← hker, MonoidHom.mem_ker]
      exact hαw
    obtain ⟨f, hf⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2) ⟨⟨w, hwK⟩, hwpc⟩
    have hwf : w ^ 2 ^ f = 1 := by
      have h := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : ↥K) : G)) hf
      simpa using h
    refine ⟨e + f, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact hwf
  have hCle : C ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCX hXC hCp
  exact hCle ((hC y).mpr ⟨hy, hcomm⟩)

end CFSG.Quasithin.H13.Ch4.NSB
