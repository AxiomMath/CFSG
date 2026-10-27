module

public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.Quasithin.TauCetiK

open CFSG.Assembly CFSG.Open.SQTKTauCeti

theorem inCatalog_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : InCatalog B) :
    InCatalog A :=
  inCatalog_isoInvariant e h

theorem nonab_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a :=
  CFSG.KCore.nonabelian_of_mulEquiv e.symm h

@[expose] def KGroupSec (G : Type) [Group G] : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup ↥H) [N.Normal], IsSimpleGroup (↥H ⧸ N) →
    (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → InCatalog (↥H ⧸ N)

theorem kGroup_iff_sec {G : Type} [Group G] : KGroup G ↔ KGroupSec G :=
  ⟨fun hK H N _ _ hnonab => CFSG.KCore.KGroupNonab.catalogue_of_surjective inCatalog_isoInvariant
    hK H hnonab (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N),
    fun hS H N _ _ hsimple hnonab => hS H (N.subgroupOf H) hsimple hnonab⟩

theorem KGroupSec.inCatalog_of_surjective {G : Type} [Group G] (hG : KGroupSec G)
    (K : Subgroup G) {S : Type} [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (φ : ↥K →* S) (hφ : Function.Surjective φ) : InCatalog S :=
  CFSG.KCore.KGroupNonab.catalogue_of_surjective inCatalog_isoInvariant (kGroup_iff_sec.mpr hG) K
    hnonab φ hφ

theorem KGroupSec.subgroup {G : Type} [Group G] (hG : KGroupSec G) (Y : Subgroup G) :
    KGroupSec ↥Y :=
  kGroup_iff_sec.mp
    (CFSG.KCore.KGroupNonab.subgroup inCatalog_isoInvariant (kGroup_iff_sec.mpr hG) Y)

theorem KGroupSec.quotient {G : Type} [Group G] (hG : KGroupSec G) (M : Subgroup G) [M.Normal] :
    KGroupSec (G ⧸ M) :=
  kGroup_iff_sec.mp
    (CFSG.KCore.KGroupNonab.quotient inCatalog_isoInvariant (kGroup_iff_sec.mpr hG) M)

theorem kGroup_subgroup {G : Type} [Group G] (hG : KGroup G) (Y : Subgroup G) : KGroup ↥Y :=
  CFSG.KCore.KGroupNonab.subgroup inCatalog_isoInvariant hG Y

theorem kGroup_quotient {G : Type} [Group G] (hG : KGroup G) (M : Subgroup G) [M.Normal] :
    KGroup (G ⧸ M) :=
  CFSG.KCore.KGroupNonab.quotient inCatalog_isoInvariant hG M

theorem kGroup_of_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (hB : KGroup B) : KGroup A :=
  CFSG.KCore.KGroupNonab.of_injective inCatalog_isoInvariant hB f hf

end CFSG.Quasithin.TauCetiK
