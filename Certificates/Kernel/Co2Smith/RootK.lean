module

public import Certificates.Kernel.Co2Smith.RootDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

theorem rootPar_k : rootParK = true := by decide +kernel

theorem find?_filterF {α : Type} (p q : α → Bool) :
    ∀ l : List α, (l.filter q).find? p = l.find? (fun x => q x && p x)
  | [] => rfl
  | x :: l => by
    cases hq : q x <;> cases hp : p x <;> simp [hq, hp, find?_filterF p q l]

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native in
@[expose] noncomputable def rootCommKF : Bool :=
  (List.range 18).all fun a => (fun Ta => (List.range 18).all fun b => (fun Tab =>
    a == b || glOpp a b || (glParams a).all fun s => (glParams b).all fun t =>
      eqK (comm4K (rootK a s) (rootK b t))
        (prodK (((Tab.find? fun e => e.2.2.1 == s && e.2.2.2.1 == t).map fun e => e.2.2.2.2).getD [])))
    (Ta.filter fun e => e.2.1 == b)) (glCommTable.filter fun e => e.1 == a)

open CFSG.Sporadic.Co2Smith.Native in
theorem rootCommK_eqF : rootCommK = rootCommKF := by
  unfold rootCommK rootCommKF glCommLookup
  simp only [find?_filterF, Bool.and_assoc]

theorem rootCommF_k : rootCommKF = true := by decide +kernel

theorem rootComm_k : rootCommK = true := by
  rw [rootCommK_eqF]
  exact rootCommF_k

theorem chart_k : chartK = true := by decide +kernel

theorem uOK_k : uOKK = true := by decide +kernel

theorem frame_k : frameK = true := by decide +kernel

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith in
theorem root_neg : (!eqK (mulV (rootK 0 1) (rootK 0 1)) (rootK 0 1) && !mapsK uK 80 81 &&
    !commK alK gaK && !eqK (comm4K (rootK 0 1) (rootK 12 1)) (rootK 0 1)) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
