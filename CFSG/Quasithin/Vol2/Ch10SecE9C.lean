module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Alike

variable {G : Type} [Group G] {Kc : Subgroup G} {Q : Type} [Group Q]

@[expose] def Alike (φ : ↥Kc →* Q) (g h : G) : Prop :=
  ∀ (z : G) (_hz : z ∈ Kc) (hg : g * z * g⁻¹ ∈ Kc) (hh : h * z * h⁻¹ ∈ Kc),
    φ ⟨g * z * g⁻¹, hg⟩ = φ ⟨h * z * h⁻¹, hh⟩

theorem map_congr_val (f : ↥Kc →* Q) {x x' : G} (hx : x ∈ Kc) (hx' : x' ∈ Kc) (h : x = x') :
    f ⟨x, hx⟩ = f ⟨x', hx'⟩ := by
  subst h; rfl

theorem conj_mem_of_mem_normalizer {g x : G} (hg : g ∈ Subgroup.normalizer (Kc : Set G))
    (hx : x ∈ Kc) : g * x * g⁻¹ ∈ Kc :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem Alike.refl (φ : ↥Kc →* Q) (g : G) : Alike φ g g := fun _ _ _ _ => rfl

variable {φ : ↥Kc →* Q} (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc)
  (hO : ∀ k : ↥Kc, (k : G) ∈ pCoreOf 2 Kc → φ k = 1)
include hker hO

theorem map_conj_congr {g : G} (hg : g ∈ Subgroup.normalizer (Kc : Set G)) {a b : G}
    (ha : a ∈ Kc) (hb : b ∈ Kc) (hab : φ ⟨a, ha⟩ = φ ⟨b, hb⟩) (ha' : g * a * g⁻¹ ∈ Kc)
    (hb' : g * b * g⁻¹ ∈ Kc) : φ ⟨g * a * g⁻¹, ha'⟩ = φ ⟨g * b * g⁻¹, hb'⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : φ (⟨a, ha⟩ * (⟨b, hb⟩ : ↥Kc)⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : a * b⁻¹ ∈ pCoreOf 2 Kc := hker _ h1
  have h3 : g * (a * b⁻¹) * g⁻¹ ∈ pCoreOf 2 Kc :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Kc hg) _).mp h2
  have e : g * (a * b⁻¹) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
  rw [e] at h3
  have h4 := hO (⟨g * a * g⁻¹, ha'⟩ * (⟨g * b * g⁻¹, hb'⟩ : ↥Kc)⁻¹) h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem Alike.mul {g g' h h' : G} (hg : g ∈ Subgroup.normalizer (Kc : Set G))
    (hg' : g' ∈ Subgroup.normalizer (Kc : Set G)) (hh : h ∈ Subgroup.normalizer (Kc : Set G))
    (hh' : h' ∈ Subgroup.normalizer (Kc : Set G)) (h₁ : Alike φ g g') (h₂ : Alike φ h h') :
    Alike φ (g * h) (g' * h') := by
  intro z hz hgh hgh'
  have hhz := conj_mem_of_mem_normalizer hh hz
  have hhz' := conj_mem_of_mem_normalizer hh' hz
  have e1 : g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
  have e2 : g' * h' * z * (g' * h')⁻¹ = g' * (h' * z * h'⁻¹) * g'⁻¹ := by group
  rw [map_congr_val φ hgh (conj_mem_of_mem_normalizer hg hhz) e1,
    map_congr_val φ hgh' (conj_mem_of_mem_normalizer hg' hhz') e2,
    h₁ _ hhz _ (conj_mem_of_mem_normalizer hg' hhz)]
  exact map_conj_congr hker hO hg' hhz hhz' (h₂ z hz hhz hhz') _ _

theorem Alike.inv {g g' : G} (hg : g ∈ Subgroup.normalizer (Kc : Set G))
    (hg' : g' ∈ Subgroup.normalizer (Kc : Set G)) (h : Alike φ g g') : Alike φ g⁻¹ g'⁻¹ := by
  intro z hz h1 h2
  have hgi := Subgroup.inv_mem _ hg
  have hgi' := Subgroup.inv_mem _ hg'
  have hw : g'⁻¹ * z * g'⁻¹⁻¹ ∈ Kc := conj_mem_of_mem_normalizer hgi' hz
  have hgw := conj_mem_of_mem_normalizer hg hw
  have h3 := h _ hw hgw (conj_mem_of_mem_normalizer hg' hw)
  have e1 : g' * (g'⁻¹ * z * g'⁻¹⁻¹) * g'⁻¹ = z := by group
  rw [map_congr_val φ (conj_mem_of_mem_normalizer hg' hw) hz e1] at h3
  have h4 := map_conj_congr hker hO hgi hz hgw h3.symm h1 (conj_mem_of_mem_normalizer hgi hgw)
  rw [h4]
  exact map_congr_val φ _ _ (by group)

theorem Alike.comm {y n t : G} (hy : y ∈ Subgroup.normalizer (Kc : Set G))
    (hn : n ∈ Subgroup.normalizer (Kc : Set G)) (ht : t ∈ Subgroup.normalizer (Kc : Set G))
    (h : Alike φ y n) : Alike φ (y * t * y⁻¹ * t⁻¹) (n * t * n⁻¹ * t⁻¹) := by
  have hyi := Subgroup.inv_mem _ hy
  have hni := Subgroup.inv_mem _ hn
  have hti := Subgroup.inv_mem _ ht
  have h1 := Alike.mul hker hO hy hn ht ht h (Alike.refl φ t)
  have h2 := Alike.mul hker hO (Subgroup.mul_mem _ hy ht) (Subgroup.mul_mem _ hn ht) hyi hni h1
    (Alike.inv hker hO hy hn h)
  exact Alike.mul hker hO (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy ht) hyi)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn ht) hni) hti hti h2 (Alike.refl φ t⁻¹)

omit hker hO in
theorem map_conj_of_mem {y z : G} (hy : y ∈ Kc) (hz : z ∈ Kc) (h : y * z * y⁻¹ ∈ Kc) :
    φ ⟨y * z * y⁻¹, h⟩ = φ ⟨y, hy⟩ * φ ⟨z, hz⟩ * (φ ⟨y, hy⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

end Alike

variable {G : Type} [Group G] [Finite G] {Kc : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂]

theorem mem_of_conj_eq_inner {φ : ↥Kc →* Q₁ × Q₂} (hφ : Function.Surjective φ)
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc)
    (hZ : Subgroup.center (Q₁ × Q₂) = ⊥) {S : Subgroup G} (hS : IsSylowTwoOf S Kc)
    (h₁ : ∀ u : Q₁, u ∈ Subgroup.normalizer
        (((S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) : Subgroup Q₁) : Set Q₁) →
      ∀ k : ℕ, u ^ 2 ^ k = 1 → u ∈ (S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ))
    (h₂ : ∀ u : Q₂, u ∈ Subgroup.normalizer
        (((S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) : Subgroup Q₂) : Set Q₂) →
      ∀ k : ℕ, u ^ 2 ^ k = 1 → u ∈ (S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ))
    {d c : G} (hdK : d ∈ Subgroup.normalizer (Kc : Set G)) {k : ℕ} (hd2 : d ^ 2 ^ k = 1)
    (hdS : ∀ x ∈ S, d * x * d⁻¹ ∈ S) (hc : c ∈ Kc)
    (hdc : ∀ (z : G) (hz : z ∈ Kc) (hz' : d * z * d⁻¹ ∈ Kc),
      φ ⟨d * z * d⁻¹, hz'⟩ = φ ⟨c, hc⟩ * φ ⟨z, hz⟩ * (φ ⟨c, hc⟩)⁻¹) : c ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := φ ⟨c, hc⟩ with hw
  obtain ⟨hSyl₁, hSyl₂, hprod⟩ := map_sylow_eq_prod hφ hS
  have hpow : ∀ j : ℕ, ∀ (z : G) (hz : z ∈ Kc) (hz' : d ^ j * z * (d ^ j)⁻¹ ∈ Kc),
      φ ⟨d ^ j * z * (d ^ j)⁻¹, hz'⟩ = w ^ j * φ ⟨z, hz⟩ * (w ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro z hz hz'; simp
    | succ j ih =>
      intro z hz hz'
      have hzj : d ^ j * z * (d ^ j)⁻¹ ∈ Kc := by
        have hpj : d ^ j ∈ Subgroup.normalizer (Kc : Set G) := Subgroup.pow_mem _ hdK j
        exact (Subgroup.mem_normalizer_iff.mp hpj z).mp hz
      have hzj' : d * (d ^ j * z * (d ^ j)⁻¹) * d⁻¹ ∈ Kc :=
        (Subgroup.mem_normalizer_iff.mp hdK _).mp hzj
      have e : d ^ (j + 1) * z * (d ^ (j + 1))⁻¹ = d * (d ^ j * z * (d ^ j)⁻¹) * d⁻¹ := by
        rw [pow_succ']; group
      rw [show (⟨d ^ (j + 1) * z * (d ^ (j + 1))⁻¹, hz'⟩ : ↥Kc) = ⟨_, hzj'⟩ from Subtype.ext e,
        hdc _ hzj hzj', ih z hz hzj, pow_succ']
      group
  have hw2 : w ^ 2 ^ k = 1 := by
    have hcen : w ^ 2 ^ k ∈ Subgroup.center (Q₁ × Q₂) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨z, hz⟩, rfl⟩ := hφ q
      have hz' : d ^ 2 ^ k * z * (d ^ 2 ^ k)⁻¹ ∈ Kc := by rw [hd2]; simpa using hz
      have h1 := hpow (2 ^ k) z hz hz'
      rw [show (⟨d ^ 2 ^ k * z * (d ^ 2 ^ k)⁻¹, hz'⟩ : ↥Kc) = ⟨z, hz⟩ from
        Subtype.ext (show d ^ 2 ^ k * z * (d ^ 2 ^ k)⁻¹ = z by rw [hd2]; group)] at h1
      calc φ ⟨z, hz⟩ * w ^ 2 ^ k = w ^ 2 ^ k * φ ⟨z, hz⟩ * (w ^ 2 ^ k)⁻¹ * w ^ 2 ^ k := by
            rw [← h1]
        _ = w ^ 2 ^ k * φ ⟨z, hz⟩ := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hwS : ∀ x ∈ (S.subgroupOf Kc).map φ, w * x * w⁻¹ ∈ (S.subgroupOf Kc).map φ := by
    rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
    have hx' : d * x * d⁻¹ ∈ Kc := (Subgroup.mem_normalizer_iff.mp hdK x).mp hxK
    refine ⟨⟨d * x * d⁻¹, hx'⟩, hdS x hx, ?_⟩
    rw [hdc x hxK hx']
  have hw₁ : w.1 ∈ (S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) := by
    refine h₁ w.1 (C10P34.mem_normalizer_of_forall_conj_mem fun u hu => ?_) k
      (by rw [← Prod.pow_fst, hw2]; rfl)
    have hu1 : (u, (1 : Q₂)) ∈ (S.subgroupOf Kc).map φ := by
      rw [hprod]; exact ⟨hu, Subgroup.one_mem _⟩
    have h1 := hwS _ hu1
    rw [hprod] at h1
    simpa using h1.1
  have hw₂ : w.2 ∈ (S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) := by
    refine h₂ w.2 (C10P34.mem_normalizer_of_forall_conj_mem fun u hu => ?_) k
      (by rw [← Prod.pow_snd, hw2]; rfl)
    have hu1 : ((1 : Q₁), u) ∈ (S.subgroupOf Kc).map φ := by
      rw [hprod]; exact ⟨Subgroup.one_mem _, hu⟩
    have h1 := hwS _ hu1
    rw [hprod] at h1
    simpa using h1.2
  have hwm : w ∈ (S.subgroupOf Kc).map φ := by rw [hprod]; exact ⟨hw₁, hw₂⟩
  obtain ⟨⟨s, hsK⟩, hs, hsw⟩ := hwm
  have hq : s⁻¹ * c ∈ pCoreOf 2 Kc := by
    have h1 : φ ((⟨s, hsK⟩ : ↥Kc)⁻¹ * ⟨c, hc⟩) = 1 := by
      rw [map_mul, map_inv, hsw, inv_mul_cancel]
    exact hker _ h1
  have hOS : pCoreOf 2 Kc ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS
  have e : c = s * (s⁻¹ * c) := by group
  rw [e]
  exact S.mul_mem (Subgroup.mem_subgroupOf.mp hs) (hOS hq)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
