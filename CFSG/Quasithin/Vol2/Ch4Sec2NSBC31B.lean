module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBC31A
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Mat

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_pCore (LH V : Subgroup G) (hVpc : V ≤ pCoreOf 2 LH) :
    V.subgroupOf LH ≤ CFSG.pCore 2 ↥LH := by
  intro w hw
  obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp (hVpc (Subgroup.mem_subgroupOf.mp hw))
  have : y = w := Subtype.ext hyw
  exact this ▸ hy

theorem card_subgroupOf {LH V : Subgroup G} (hV : V ≤ LH) :
    Nat.card ↥(V.subgroupOf LH) = Nat.card ↥V :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv

theorem subgroupOf_central (LH V : Subgroup G) (hVcent : V ≤ Subgroup.centralizer
      (pCoreOf 2 LH : Set G)) :
    ∀ w ∈ V.subgroupOf LH, ∀ o ∈ CFSG.pCore 2 ↥LH, w * o = o * w := by
  intro w hw o ho
  have hoP : (o : G) ∈ pCoreOf 2 LH := Subgroup.mem_map_of_mem LH.subtype ho
  have hc := Subgroup.mem_centralizer_iff.mp (hVcent (Subgroup.mem_subgroupOf.mp hw))
    (o : G) hoP
  exact Subtype.ext (hc.symm)

@[expose] def phiImage (K LH : Subgroup G) (hLK : LH ≤ K) : ↥LH →* ↥(imageModCenter K LH) :=
  ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hLK)).codRestrict
    (imageModCenter K LH) fun x => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)

theorem phiImage_val (K LH : Subgroup G) (hLK : LH ≤ K) (x : ↥LH) :
    ((phiImage K LH hLK x : ↥(imageModCenter K LH)) : ↥K ⧸ Subgroup.center ↥K) =
      QuotientGroup.mk' (Subgroup.center ↥K) (Subgroup.inclusion hLK x) := rfl

theorem phiImage_surjective (K LH : Subgroup G) (hLK : LH ≤ K) :
    Function.Surjective (phiImage K LH hLK) := by
  rintro ⟨b, hb⟩
  unfold imageModCenter at hb
  obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.mp hb
  exact ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, Subtype.ext hzb⟩

theorem mem_centerOf_of_phiImage_eq_one (K LH : Subgroup G) (hLK : LH ≤ K) {x : ↥LH}
    (h : phiImage K LH hLK x = 1) : (x : G) ∈ centerOf K := by
  have h2 : QuotientGroup.mk' (Subgroup.center ↥K) (Subgroup.inclusion hLK x) = 1 := by
    rw [← phiImage_val]
    exact congrArg Subtype.val h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  refine Subgroup.mem_inf.mpr ⟨hLK x.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hc := Subgroup.mem_center_iff.mp h2 ⟨k, hk⟩
  exact congrArg Subtype.val hc

theorem isPGroup_ker_phiImage (K LH : Subgroup G) (hLK : LH ≤ K)
    (hZ2 : IsPGroup 2 ↥(centerOf K)) : IsPGroup 2 ↥(phiImage K LH hLK).ker := by
  rw [isPGroup_iff_pow]
  intro x hx
  have hxZ : (x : G) ∈ centerOf K := mem_centerOf_of_phiImage_eq_one K LH hLK
    (MonoidHom.mem_ker.mp hx)
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow.mp hZ2) (x : G) hxZ
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem isPGroup_ker_id (LH : Subgroup G) : IsPGroup 2 ↥(MonoidHom.id ↥LH).ker := by
  rw [isPGroup_iff_pow]
  intro x hx
  have h1 : x = 1 := MonoidHom.mem_ker.mp hx
  exact ⟨0, by simp [h1]⟩

theorem ratio_D (LH : Subgroup G) (N : Subgroup ↥LH) [N.Normal] (hN : IsPGroup 2 ↥N) :
    ∃ e : ℕ, Nat.card (↥LH ⧸ N) = Nat.card (ModO2 LH) * 2 ^ e := by
  obtain ⟨e, he, -⟩ := ratio_of_hom (MonoidHom.id ↥LH) (fun x => ⟨x, rfl⟩)
    (isPGroup_ker_id LH) N hN
  exact ⟨e, he⟩

theorem ratio_I (K LH : Subgroup G) (hLK : LH ≤ K) (hZ2 : IsPGroup 2 ↥(centerOf K))
    (N : Subgroup ↥(imageModCenter K LH)) [N.Normal] (hN : IsPGroup 2 ↥N) :
    ∃ e : ℕ, Nat.card (↥(imageModCenter K LH) ⧸ N) = Nat.card (ModO2 LH) * 2 ^ e := by
  obtain ⟨e, he, -⟩ := ratio_of_hom (phiImage K LH hLK) (phiImage_surjective K LH hLK)
    (isPGroup_ker_phiImage K LH hLK hZ2) N hN
  exact ⟨e, he⟩

theorem card_V_le_D {LH V : Subgroup G} (hV : V ≤ LH) (hVpc : V ≤ pCoreOf 2 LH)
    (N : Subgroup ↥LH) [N.Normal] (hN : IsPGroup 2 ↥N)
    (hy : Nat.card (↥LH ⧸ N) = Nat.card (ModO2 LH)) : Nat.card V ≤ Nat.card N := by
  obtain ⟨-, -, hO⟩ := ratio_of_hom (MonoidHom.id ↥LH) (fun x => ⟨x, rfl⟩)
    (isPGroup_ker_id LH) N hN
  have h := card_le_of_pCore_eq (MonoidHom.id ↥LH) (fun x => ⟨x, rfl⟩) N (hO hy)
    (V.subgroupOf LH) (subgroupOf_le_pCore LH V hVpc) (fun w _ h => h)
  rwa [card_subgroupOf hV] at h

theorem card_V_le_center_D {LH V : Subgroup G} (hV : V ≤ LH) (hVpc : V ≤ pCoreOf 2 LH)
    (hVcent : V ≤ Subgroup.centralizer (pCoreOf 2 LH : Set G))
    (N : Subgroup ↥LH) [N.Normal] (hN : IsPGroup 2 ↥N)
    (hy : Nat.card (↥LH ⧸ N) = Nat.card (ModO2 LH)) :
    Nat.card V ≤ Nat.card (Subgroup.center ↥N) := by
  obtain ⟨-, -, hO⟩ := ratio_of_hom (MonoidHom.id ↥LH) (fun x => ⟨x, rfl⟩)
    (isPGroup_ker_id LH) N hN
  have h := card_le_center_of_pCore_eq (MonoidHom.id ↥LH) (fun x => ⟨x, rfl⟩) N (hO hy)
    (V.subgroupOf LH) (subgroupOf_le_pCore LH V hVpc) (subgroupOf_central LH V hVcent)
    (fun w _ h => h)
  rwa [card_subgroupOf hV] at h

theorem card_V_le_I (K LH V : Subgroup G) (hLK : LH ≤ K) (hZ2 : IsPGroup 2 ↥(centerOf K))
    (hVinf : V ⊓ centerOf K = ⊥) (hV : V ≤ LH) (hVpc : V ≤ pCoreOf 2 LH)
    (N : Subgroup ↥(imageModCenter K LH)) [N.Normal] (hN : IsPGroup 2 ↥N)
    (hy : Nat.card (↥(imageModCenter K LH) ⧸ N) = Nat.card (ModO2 LH)) :
    Nat.card V ≤ Nat.card N := by
  obtain ⟨-, -, hO⟩ := ratio_of_hom (phiImage K LH hLK) (phiImage_surjective K LH hLK)
    (isPGroup_ker_phiImage K LH hLK hZ2) N hN
  have hWφ : ∀ w ∈ V.subgroupOf LH, phiImage K LH hLK w = 1 → w = 1 := by
    intro w hw h
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have hwZ := mem_centerOf_of_phiImage_eq_one K LH hLK h
    have h1 : (w : G) ∈ V ⊓ centerOf K := Subgroup.mem_inf.mpr ⟨hwV, hwZ⟩
    rw [hVinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have h := card_le_of_pCore_eq (phiImage K LH hLK) (phiImage_surjective K LH hLK) N (hO hy)
    (V.subgroupOf LH) (subgroupOf_le_pCore LH V hVpc) hWφ
  rwa [card_subgroupOf hV] at h

theorem card_V_le_center_I (K LH V : Subgroup G) (hLK : LH ≤ K) (hZ2 : IsPGroup 2 ↥(centerOf K))
    (hVinf : V ⊓ centerOf K = ⊥) (hV : V ≤ LH) (hVpc : V ≤ pCoreOf 2 LH)
    (hVcent : V ≤ Subgroup.centralizer (pCoreOf 2 LH : Set G))
    (N : Subgroup ↥(imageModCenter K LH)) [N.Normal] (hN : IsPGroup 2 ↥N)
    (hy : Nat.card (↥(imageModCenter K LH) ⧸ N) = Nat.card (ModO2 LH)) :
    Nat.card V ≤ Nat.card (Subgroup.center ↥N) := by
  obtain ⟨-, -, hO⟩ := ratio_of_hom (phiImage K LH hLK) (phiImage_surjective K LH hLK)
    (isPGroup_ker_phiImage K LH hLK hZ2) N hN
  have hWφ : ∀ w ∈ V.subgroupOf LH, phiImage K LH hLK w = 1 → w = 1 := by
    intro w hw h
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have hwZ := mem_centerOf_of_phiImage_eq_one K LH hLK h
    have h1 : (w : G) ∈ V ⊓ centerOf K := Subgroup.mem_inf.mpr ⟨hwV, hwZ⟩
    rw [hVinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have h := card_le_center_of_pCore_eq (phiImage K LH hLK) (phiImage_surjective K LH hLK) N
    (hO hy) (V.subgroupOf LH) (subgroupOf_le_pCore LH V hVpc)
    (subgroupOf_central LH V hVcent) hWφ
  rwa [card_subgroupOf hV] at h

theorem false_of_prime_dvd {q y s e : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hy : y = s * 2 ^ e)
    (hqy : q ∣ y) (hqs : ¬ q ∣ s) : False := by
  rw [hy] at hqy
  rcases (Nat.Prime.dvd_mul hq).mp hqy with h | h
  · exact hqs h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))

theorem false_of_lt {y s e : ℕ} (hy : y = s * 2 ^ e) (hlt : y < s) : False := by
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h2 : s ≤ s * 2 ^ e := Nat.le_mul_of_pos_right s (by omega)
  omega

end CFSG.Quasithin.H13.Ch4.NSB
