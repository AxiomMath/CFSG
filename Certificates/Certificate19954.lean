module

public import CFSG.Quasithin.Recognition.CertD4BridgeDataInputs

public section

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Ree

namespace CertificateChecks.Batch19954

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Ree

private theorem d4b_checkX0_0 : D4bXOK ⟨0, by decide⟩ := by
  unfold D4bXOK
  decide +kernel

private theorem d4b_checkX1_1 : D4bXOK ⟨1, by decide⟩ := by
  unfold D4bXOK
  decide +kernel

private theorem d4b_checkX2_2 : D4bXOK ⟨2, by decide⟩ := by
  unfold D4bXOK
  decide +kernel

private theorem d4b_checkX3_3 : D4bXOK ⟨3, by decide⟩ := by
  unfold D4bXOK
  decide +kernel

private theorem d4b_checkY0_4 : D4bYOK ⟨0, by decide⟩ := by
  unfold D4bYOK
  decide +kernel

private theorem d4b_checkY1_5 : D4bYOK ⟨1, by decide⟩ := by
  unfold D4bYOK
  decide +kernel

private theorem d4b_checkY2_6 : D4bYOK ⟨2, by decide⟩ := by
  unfold D4bYOK
  decide +kernel

private theorem d4b_checkY3_7 : D4bYOK ⟨3, by decide⟩ := by
  unfold D4bYOK
  decide +kernel

private theorem d4bEs_mul_self_8 :
    ∀ (i : Fin Tag.D4.rank) (s : Bool), d4bEs i s * d4bEs i s = 0 := by
  decide +kernel

private theorem d4bSimple_root_9 : ∀ (i : Fin Tag.D4.rank) (s : Bool),
    d4Certificate.root (d4bSimple i s) = (if s then 1 else -1) • Pi.single i 1 := by
  decide +kernel

private theorem d4b_root_injective_10 : ∀ m n : Fin d4Certificate.roots.length,
    d4Certificate.root m = d4Certificate.root n → m = n := by
  decide +kernel

end CertificateChecks.Batch19954

namespace Certificates

open CertificateChecks

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Ree in
theorem certificate19954 : (D4bXOK ⟨0, by decide⟩)
    ∧ (D4bXOK ⟨1, by decide⟩)
    ∧ (D4bXOK ⟨2, by decide⟩)
    ∧ (D4bXOK ⟨3, by decide⟩)
    ∧ (D4bYOK ⟨0, by decide⟩)
    ∧ (D4bYOK ⟨1, by decide⟩)
    ∧ (D4bYOK ⟨2, by decide⟩)
    ∧ (D4bYOK ⟨3, by decide⟩)
    ∧ (∀ (i : Fin Tag.D4.rank) (s : Bool), d4bEs i s * d4bEs i s = 0)
    ∧ (∀ (i : Fin Tag.D4.rank) (s : Bool),
          d4Certificate.root (d4bSimple i s) = (if s then 1 else -1) • Pi.single i 1)
    ∧ (∀ m n : Fin d4Certificate.roots.length,
          d4Certificate.root m = d4Certificate.root n → m = n) := by
  exact ⟨@CertificateChecks.Batch19954.d4b_checkX0_0, @CertificateChecks.Batch19954.d4b_checkX1_1, @CertificateChecks.Batch19954.d4b_checkX2_2,
    @CertificateChecks.Batch19954.d4b_checkX3_3, @CertificateChecks.Batch19954.d4b_checkY0_4, @CertificateChecks.Batch19954.d4b_checkY1_5,
    @CertificateChecks.Batch19954.d4b_checkY2_6, @CertificateChecks.Batch19954.d4b_checkY3_7, @CertificateChecks.Batch19954.d4bEs_mul_self_8,
    @CertificateChecks.Batch19954.d4bSimple_root_9, @CertificateChecks.Batch19954.d4b_root_injective_10⟩

end Certificates
