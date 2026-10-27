module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4H
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4F
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4G

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.A4

@[expose] def J4KXNormal6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
    Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K →
    C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K →
    ∀ r : G, r ∈ pCoreOf 2 I ⊓ Subgroup.centralizer (K : Set G) → r ≠ 1 → r * r = 1 →
      I ≤ Subgroup.centralizer ({r} : Set G) →
    ∀ x ∈ perfectCore (L ⊓ H), orderOf x = 3 →
      CFSG.IsQuasisimple ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) →
      Nat.card ↥(Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) = 6 →
      IsSporadic .M22 (↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) ⧸
        Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) →
      Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer (perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem false_of_inner6
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOut : J4OutTrivial)
    (hBlk : J4BlockFacts) (hKX : J4KXNormal6) {T M L Mm I H K : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) (hILT : I ≤ L ⊔ T) (hTin : T ≤ L ⊔ pCoreOf 2 (L ⊔ T)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  set R := pCoreOf 2 I with hR
  set R₁ := pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (R : Set G) with hR₁
  obtain ⟨r, hrRC, hr1, hr2, hrI, hrR₁⟩ := exists_r h37 h38 h39 hOut hBlk hy hIH c h6 hILT
  have hker := inf_centralizer_le h37 h38 h39 hy c hrRC.2 hr1 hr2 hrI
  have hlt := lt_inf_normalizer (pCoreOf_lt h37 h38 h39 hy hIH c hTin)
  have hsurj := exists_comm_eq hBlk hy hIH c h6 hrI hrR₁ hker hlt
  have hLHI : LH ≤ I := LH_le hy hIH c
  obtain ⟨-, -, -, x, hxLH, hx3, -, hq, hcard, hM22, hnot⟩ := blockFacts_of_case6 hBlk c h6
  set KX := perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) with hKX'
  obtain ⟨v, ⟨hvE, hvx⟩, hvK⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨s₀, hs₀, hs₀v⟩ := hsurj v hvE
  have hxI : x ∈ I := hLHI hxLH
  have hxR₁ : x ∈ Subgroup.normalizer (R₁ : Set G) :=
    mem_normalizer_inf (le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left ((perfectCore_le (L ⊓ H)).trans inf_le_left hxLH)))
      (Subgroup.le_normalizer (le_normalizer_pCoreOf 2 I hxI))
  have hxr : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp (hrI hxI)
  have hxv : x * v = v * x := (Subgroup.mem_centralizer_singleton_iff.mp hvx).symm
  have hRR₁ : R ≤ R₁ := le_inf c.R_le Subgroup.le_normalizer
  have hRr : R ≤ Subgroup.centralizer ({r} : Set G) := (pCoreOf_le 2 I).trans hrI
  obtain ⟨s, -, hsx, hsv⟩ := exists_mem_centralizer_comm_eq (pCoreOf_isPGroup 2 I) hRR₁ hRr
    hker hx3 hxR₁ hxr hxv hs₀ hs₀v
  have hsN : s ∈ Subgroup.normalizer (KX : Set G) :=
    hKX G T M L Mm I H K hy hIH c h6 r hrRC hr1 hr2 hrI x hxLH hx3 hq hcard hM22
      (Subgroup.mem_centralizer_singleton_iff.mpr hsx)
  have hKXK : KX ≤ K := (perfectCore_le _).trans inf_le_left
  have hry : ∀ z ∈ KX, z * r = r * z := fun z hz =>
    Subgroup.mem_centralizer_iff.mp hrRC.2 z (hKXK hz)
  apply hvK
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : s⁻¹ * y * s ∈ KX := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) y).mp hy
    simpa using this
  have h1 := hry _ hy'
  have h2 := hry y hy
  have h3 : y * (s * r * s⁻¹) = (s * r * s⁻¹) * y := by
    calc y * (s * r * s⁻¹) = s * (s⁻¹ * y * s * r) * s⁻¹ := by group
      _ = s * (r * (s⁻¹ * y * s)) * s⁻¹ := by rw [h1]
      _ = (s * r * s⁻¹) * y := by group
  have h4 : y * r⁻¹ = r⁻¹ * y := by
    calc y * r⁻¹ = r⁻¹ * (r * y) * r⁻¹ := by group
      _ = r⁻¹ * (y * r) * r⁻¹ := by rw [h2]
      _ = r⁻¹ * y := by group
  rw [← hsv]
  calc y * (s * r * s⁻¹ * r⁻¹) = (y * (s * r * s⁻¹)) * r⁻¹ := by group
    _ = (s * r * s⁻¹) * y * r⁻¹ := by rw [h3]
    _ = (s * r * s⁻¹) * (y * r⁻¹) := by group
    _ = (s * r * s⁻¹) * (r⁻¹ * y) := by rw [h4]
    _ = s * r * s⁻¹ * r⁻¹ * y := by group

end NoJ4

end CFSG.Quasithin.H13.Ch4
