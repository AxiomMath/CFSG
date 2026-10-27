module

public import CFSG.Sporadic.Th.Certificate
public import CFSG.Sporadic.Th.KernelSimple

public section

namespace CFSG.Milestones

theorem fam_th_simplicity :
    IsSimpleGroup Blueprint.NativeSporadic.Th :=
  Sporadic.Th.Kernel.isSimpleGroup_Th Sporadic.Th.th_kernel_facts

end CFSG.Milestones
